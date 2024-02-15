#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <inttypes.h>
#include <gmp.h>

#include "CRPC.h"
#include "config.h"
#include "circuit.h"
#include "list_tuples.h"
#include "combinations.h"
#include "coeffs.h"
#include "verification_rules.h"
#include "dimensions.h"
#include "constructive.h"



struct callback_data {
  uint64_t* coeffs;
  int t;
  int nb_duplications;
};


static int generate_names(ParsedFile * pf, char *** names_ptr){

  int length = pf->randoms->next_val + pf->eqs->size;
  
  *names_ptr = malloc(length * sizeof(**names_ptr));
  char ** names = *names_ptr;

  int idx = 0;
  StrMapElem * elem = pf->randoms->head;
  while(elem){
    names[idx] = strdup(elem->key);
    idx++;
    elem = elem->next;
  }

  EqListElem * elem_eq = pf->eqs->head;
  while(elem_eq){
    names[idx] = strdup(elem_eq->dst);
    idx++;
    elem_eq = elem_eq->next;
  }

  return length;
}

static void update_coeffs(const Circuit* c, Comb* comb, int comb_len, SecretDep* secret_deps,
                          void* data_void) {
  (void) secret_deps;
  struct callback_data* data = (struct callback_data*) data_void;
  int t = data->t;
  int nb_duplications = data->nb_duplications;

  update_coeff_c_single(c, data->coeffs, &comb[t*nb_duplications], comb_len-(t*nb_duplications));
}

void construct_output_prefix(Circuit * c, StrMap * out, Comb * out_comb, Comb * out_comb_res, int t){

  char ** names = malloc(t*c->nb_duplications * sizeof(*names));
  for(int i=0; i<t; i++){
    for(int j=0; j<c->nb_duplications; j++){
      names[i*c->nb_duplications + j] = malloc(10 * sizeof(*names[i*c->nb_duplications + j]));
      sprintf(names[i*c->nb_duplications + j], "%s%d_%d", out->head->key, out_comb[i], j);
    }
  }
  DependencyList * deps = c->deps;
  int idx = 0;
  for(int i= c->length; i< deps->length; i++){

    for(int j= 0; j< t*c->nb_duplications; j++){
      if(strcmp(names[j], deps->names[i]) == 0){
        // printf("%s\n", names[j]);
        out_comb_res[idx] = i;
        idx++;
        break;
      }
    }
  }
  assert(idx == t * c->nb_duplications);

  for(int i=0; i<t*c->nb_duplications; i++){
    free(names[i]);
  }
  free(names);

}

static void get_filename(ParsedFile * pf, int coeff_max, int t, int k, bool set, char **name){
  *name = malloc(strlen(pf->filename) + 60);
  sprintf(*name, "%s_t%d_k%d_c%d_f%d.CRPC_coeffs", pf->filename, t, k, coeff_max, set ? 1 : 0);
}

static void get_faulty_combs_filename(ParsedFile * pf, int k, bool set, char **name){
  *name = malloc(strlen(pf->filename) + 50);
  sprintf(*name, "%s_faulty_scenarios_k%d_f%d_CRPC", pf->filename, k, set ? 1 : 0);
}

void compute_CRPC_coeffs(ParsedFile * pf, int cores, int coeff_max, int k, int t, bool set) {

  if(pf->out->next_val > 1){
    fprintf(stderr, "Cannot verify CRPC for gadgets with more than 1 output.");
    exit(EXIT_FAILURE);
  }

  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;
  if(coeff_max == -1){
    coeff_max = c->length;
  }
  free_circuit(c);

  char * faulty_combs_filename;
  get_faulty_combs_filename(pf, k, set, &faulty_combs_filename);

  FILE * faulty_combs_file = fopen(faulty_combs_filename, "r");
  if(!faulty_combs_file){
    fprintf(stderr, "You must execute the testing_correction.py first on your gadget to generate the %s file.\n", faulty_combs_filename);
    free(faulty_combs_filename);
    exit(EXIT_FAILURE);
  }
  free(faulty_combs_filename);
  int nb_input_combs;
  fscanf(faulty_combs_file, " %d", &nb_input_combs);
  printf("There are %d input combs to consider\n", nb_input_combs);

  uint64_t out_comb_len;
  Comb** out_comb_arr = gen_combinations(&out_comb_len, t, pf->shares - 1);
  Comb * out_comb = malloc((t * pf->nb_duplications) * sizeof(*out_comb));

  VarVector verif_prefix = { .length = t*pf->nb_duplications, 
                             .max_size = t*pf->nb_duplications, 
                             .content = NULL };

  struct callback_data data = { .t = t, .coeffs = NULL, .nb_duplications = pf->nb_duplications };

  char * filename;
  get_filename(pf, coeff_max, t, k, set, &filename);
  FILE * coeffs_file = fopen(filename, "wb");
  free(filename);

  for(int i=0; i< nb_input_combs; i++){
    // Constructing input faults prefix
    int size_input_comb;
    fscanf(faulty_combs_file, " %d ,", &size_input_comb);
    printf("%d, ", size_input_comb);
    FaultedVar ** v_inps = malloc(size_input_comb * sizeof(*v_inps));
    for(int k=0; k<size_input_comb-1; k++){
      v_inps[k] = malloc(sizeof(*v_inps[k]));
      v_inps[k]->name = malloc(60 * sizeof(*v_inps[k]->name));
      fscanf(faulty_combs_file, " %[^,],", v_inps[k]->name);
      v_inps[k]->set = set;
      v_inps[k]->fault_on_input = true;
      sscanf(v_inps[k]->name, "%*[a-zA-Z]%d_%d", &v_inps[k]->share, &v_inps[k]->duplicate);
      printf("%s %d %d, ", v_inps[k]->name, v_inps[k]->share, v_inps[k]->duplicate);
    }
    v_inps[size_input_comb-1] = malloc(sizeof(*v_inps[size_input_comb-1]));
    v_inps[size_input_comb-1]->name = malloc(60 * sizeof(*v_inps[size_input_comb-1]->name));
    fscanf(faulty_combs_file, " %s", v_inps[size_input_comb-1]->name);
    v_inps[size_input_comb-1]->set = set;
    v_inps[size_input_comb-1]->fault_on_input = true;
    sscanf(v_inps[size_input_comb-1]->name, "%*[a-zA-Z]%d_%d", &v_inps[size_input_comb-1]->share, &v_inps[size_input_comb-1]->duplicate);
    printf("%s %d %d\n", v_inps[size_input_comb-1]->name, v_inps[size_input_comb-1]->share, v_inps[size_input_comb-1]->duplicate);

    // Reading faulty scenarios to ignore with the constructed input prefix
    FaultsCombs * sfc = malloc(sizeof(*sfc));
    int nb_faulty_combs;
    fscanf(faulty_combs_file, " %d", &nb_faulty_combs);
    // printf("%d\n", nb_faulty_combs);
    sfc->length = nb_faulty_combs;
    sfc->fc = malloc(nb_faulty_combs * sizeof(*sfc->fc));
    FaultsComb ** fc = sfc->fc;
    for(int m=0; m<nb_faulty_combs; m++){
      fc[m] = malloc(sizeof(*fc[m]));
      fscanf(faulty_combs_file, " %d ,", &fc[m]->length);
      fc[m]->names = malloc(fc[m]->length * sizeof(*fc[m]->names));
      // printf("%d, ", fc[k]->length);
      for(int j=0; j< fc[m]->length-1; j++){
        fc[m]->names[j] = malloc(60 * sizeof(*fc[m]->names[j]));
        fscanf(faulty_combs_file, " %[^,],", fc[m]->names[j]);
        // printf("%s, ", fc[k]->names[j]);
      }
      fc[m]->names[fc[m]->length-1] = malloc(60 * sizeof(*fc[m]->names[fc[m]->length-1]));
      fscanf(faulty_combs_file, " %s\n", fc[m]->names[fc[m]->length-1]);
      // printf("%s\n", fc[k]->names[fc[k]->length-1]);
    }
    // printf("\n");
    // printf("k = %d\n", k);
    for(int f=1; f<=k; f++){
      Faults * fv = malloc(sizeof(*fv));
      Comb * comb = first_comb(f, 0);
      do{

        FaultedVar ** v = malloc((f+size_input_comb) * sizeof(*v));
        for(int j=0; j<f; j++){
          v[j] = malloc(sizeof(*v[j]));
          v[j]->set = set;
          v[j]->name = names[comb[j]];
          v[j]->fault_on_input = false;
        }
        for(int j=f; j<f+size_input_comb; j++){
          v[j] = malloc(sizeof(*v[j]));
          v[j]->set = set;
          v[j]->name = v_inps[j-f]->name;
          v[j]->fault_on_input = v_inps[j-f]->fault_on_input;
          v[j]->share = v_inps[j-f]->share;
          v[j]->duplicate = v_inps[j-f]->duplicate;
        }
        fv->vars = v;
        fv->length = f;
        printf("################ Cheking CRPC with faults on ");
        for(int j=0; j<f+size_input_comb; j++){
          printf("%s, ", v[j]->name);
        }
        printf("...\n");

        if(ignore_faulty_scenario(fv, sfc)){
          printf("Ignoring...\n");
          goto skip;
        }
        fv->length = f+size_input_comb;
        

        Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);

        uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));

        uint64_t** coeffs_out_comb;
        coeffs_out_comb = malloc(out_comb_len * sizeof(*coeffs_out_comb));
        for (unsigned i = 0; i < out_comb_len; i++) {
          coeffs_out_comb[i] = calloc((total_wires + 1),  sizeof(*coeffs_out_comb[i]));
        }

        for (int size = 0; size <= coeff_max; size++) {

          for (unsigned int l = 0; l < out_comb_len; l++) {
            construct_output_prefix(c, pf->out, out_comb_arr[l], out_comb, t);
            verif_prefix.content = out_comb;
            data.coeffs = coeffs_out_comb[l];

            find_all_failures(circuit,
                          cores,
                          (t == circuit->share_count) ? t-1 : t, // t_in
                          &verif_prefix,  // prefix
                          size+verif_prefix.length, // comb_len
                          size+verif_prefix.length, // max_len
                          NULL,  // dim_red_data
                          true,  // has_random
                          NULL,  // first_comb
                          false, // include_outputs
                          0,     // shares_to_ignore
                          false, // PINI
                          NULL, // incompr_tuples
                          update_coeffs,
                          (void*)&data);
          }
        }

        #define max(a,b) ((a) > (b) ? (a) : (b))
        for (int m = 0; m <= circuit->total_wires; m++) {
          for (unsigned j = 0; j < out_comb_len; j++) {
            coeffs[m] = max(coeffs[m], coeffs_out_comb[j][m]);
          }
          // printf("%"PRId64", ", coeffs[m]);
        }
        // printf("\n");
        for (unsigned i = 0; i < out_comb_len; i++) {
          free(coeffs_out_comb[i]);
        }
        free(coeffs_out_comb);


        fwrite(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
        free(coeffs);
        free_circuit(circuit);

        skip:;
        for(int j=0; j<f+size_input_comb; j++){
          free(v[j]);
        }
        free(v);
      }while(incr_comb_in_place(comb, f, length));
      free(comb);
      free(fv);
    }

    Faults * fv = malloc(sizeof(*fv));
    FaultedVar ** v = malloc(size_input_comb * sizeof(*v));
    for(int j=0; j<size_input_comb; j++){
      v[j] = malloc(sizeof(*v[j]));
      v[j]->set = set;
      v[j]->name = v_inps[j]->name;
      v[j]->fault_on_input = v_inps[j]->fault_on_input;
      v[j]->share = v_inps[j]->share;
      v[j]->duplicate = v_inps[j]->duplicate;
    }
    fv->vars = v;
    fv->length = size_input_comb;
    printf("################ Cheking CRPC without internal faults...\n");

    Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);
    uint64_t * coeffs = calloc(c->total_wires+1, sizeof(*coeffs));
    uint64_t** coeffs_out_comb;
    coeffs_out_comb = malloc(out_comb_len * sizeof(*coeffs_out_comb));
    for (unsigned i = 0; i < out_comb_len; i++) {
      coeffs_out_comb[i] = calloc((total_wires + 1),  sizeof(*coeffs_out_comb[i]));
    }

    for (int size = 0; size <= coeff_max; size++) {

      for (unsigned int l = 0; l < out_comb_len; l++) {
        construct_output_prefix(c, pf->out, out_comb_arr[l], out_comb, t);
        verif_prefix.content = out_comb;
        data.coeffs = coeffs_out_comb[l];

        find_all_failures(circuit,
                      cores,
                      (t == circuit->share_count) ? t-1 : t, // t_in
                      &verif_prefix,  // prefix
                      size+verif_prefix.length, // comb_len
                      size+verif_prefix.length, // max_len
                      NULL,  // dim_red_data
                      true,  // has_random
                      NULL,  // first_comb
                      false, // include_outputs
                      0,     // shares_to_ignore
                      false, // PINI
                      NULL, // incompr_tuples
                      update_coeffs,
                      (void*)&data);
      }
    }

    #define max(a,b) ((a) > (b) ? (a) : (b))
    for (int m = 0; m <= circuit->total_wires; m++) {
      for (unsigned j = 0; j < out_comb_len; j++) {
        coeffs[m] = max(coeffs[m], coeffs_out_comb[j][m]);
      }
      // printf("%d %"PRId64"\n", m, coeffs[m]);
    }
    for (unsigned i = 0; i < out_comb_len; i++) {
      free(coeffs_out_comb[i]);
    }
    free(coeffs_out_comb);
    fwrite(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
    free(coeffs);
    free_circuit(circuit);

    for(int j=0; j<size_input_comb; j++){
      free(v[j]);
    }
    free(v);

    for(int k=0; k<size_input_comb; k++){
      free(v_inps[k]->name);
      free(v_inps[k]);
    }
    free(v_inps);
    free_faults_combs(sfc);
  }

  fclose(coeffs_file);
  fclose(faulty_combs_file);
  for(int i=0; i<length; i++){
    free(names[i]);
  }
  free(names);
  for(uint64_t i=0; i<out_comb_len; i++){
    free(out_comb_arr[i]);
  }
  free(out_comb_arr);
  free(out_comb);



}


void compute_CRPC_val(ParsedFile * pf, int coeff_max, int k, int t, double pleak, double pfault, bool set){
  if(pf->out->next_val > 1){
    fprintf(stderr, "Cannot verify CRPC for gadgets with more than 1 output.");
    exit(EXIT_FAILURE);
  }

  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;
  if(coeff_max == -1){
    coeff_max = c->length;
  }
  free_circuit(c);

  char * faulty_combs_filename;
  get_faulty_combs_filename(pf, k, set, &faulty_combs_filename);

  FILE * faulty_combs_file = fopen(faulty_combs_filename, "r");
  if(!faulty_combs_file){
    fprintf(stderr, "You must execute the testing_correction.py first on your gadget to generate the %s file.\n", faulty_combs_filename);
    free(faulty_combs_filename);
    exit(EXIT_FAILURE);
  }
  free(faulty_combs_filename);
  int nb_input_combs;
  fscanf(faulty_combs_file, " %d", &nb_input_combs);
  printf("There are %d input combs to consider\n", nb_input_combs);

  mpf_t * epsilon, * mu, * epsilon_max, * mu_max;
  epsilon = malloc(nb_input_combs * sizeof(*epsilon));
  mu = malloc(nb_input_combs * sizeof(*mu));
  epsilon_max = malloc(nb_input_combs * sizeof(*epsilon_max));
  mu_max = malloc(nb_input_combs * sizeof(*mu_max));
  for(int i=0; i<nb_input_combs; i++){
    mpf_init(epsilon[i]);
    mpf_init(mu[i]);
    mpf_init(epsilon_max[i]);
    mpf_init(mu_max[i]);
  }
  

  char * filename;
  get_filename(pf, coeff_max, t, k, set, &filename);
  FILE * coeffs_file = fopen(filename, "rb");
  free(filename);

  for(int i=0; i< nb_input_combs; i++){
    // Constructing input faults prefix
    int size_input_comb;
    fscanf(faulty_combs_file, " %d ,", &size_input_comb);
    printf("%d, ", size_input_comb);
    FaultedVar ** v_inps = malloc(size_input_comb * sizeof(*v_inps));
    for(int k=0; k<size_input_comb-1; k++){
      v_inps[k] = malloc(sizeof(*v_inps[k]));
      v_inps[k]->name = malloc(60 * sizeof(*v_inps[k]->name));
      fscanf(faulty_combs_file, " %[^,],", v_inps[k]->name);
      v_inps[k]->set = set;
      v_inps[k]->fault_on_input = true;
      sscanf(v_inps[k]->name, "%*[a-zA-Z]%d_%d", &v_inps[k]->share, &v_inps[k]->duplicate);
      printf("%s %d %d, ", v_inps[k]->name, v_inps[k]->share, v_inps[k]->duplicate);
    }
    v_inps[size_input_comb-1] = malloc(sizeof(*v_inps[size_input_comb-1]));
    v_inps[size_input_comb-1]->name = malloc(60 * sizeof(*v_inps[size_input_comb-1]->name));
    fscanf(faulty_combs_file, " %s", v_inps[size_input_comb-1]->name);
    v_inps[size_input_comb-1]->set = set;
    v_inps[size_input_comb-1]->fault_on_input = true;
    sscanf(v_inps[size_input_comb-1]->name, "%*[a-zA-Z]%d_%d", &v_inps[size_input_comb-1]->share, &v_inps[size_input_comb-1]->duplicate);
    printf("%s %d %d\n", v_inps[size_input_comb-1]->name, v_inps[size_input_comb-1]->share, v_inps[size_input_comb-1]->duplicate);

    // Reading faulty scenarios to ignore with the constructed input prefix
    FaultsCombs * sfc = malloc(sizeof(*sfc));
    int nb_faulty_combs;
    fscanf(faulty_combs_file, " %d", &nb_faulty_combs);
    // printf("%d\n", nb_faulty_combs);
    sfc->length = nb_faulty_combs;
    sfc->fc = malloc(nb_faulty_combs * sizeof(*sfc->fc));
    FaultsComb ** fc = sfc->fc;
    for(int m=0; m<nb_faulty_combs; m++){
      fc[m] = malloc(sizeof(*fc[m]));
      fscanf(faulty_combs_file, " %d ,", &fc[m]->length);
      fc[m]->names = malloc(fc[m]->length * sizeof(*fc[m]->names));
      // printf("%d, ", fc[k]->length);
      for(int j=0; j< fc[m]->length-1; j++){
        fc[m]->names[j] = malloc(60 * sizeof(*fc[m]->names[j]));
        fscanf(faulty_combs_file, " %[^,],", fc[m]->names[j]);
        // printf("%s, ", fc[k]->names[j]);
      }
      fc[m]->names[fc[m]->length-1] = malloc(60 * sizeof(*fc[m]->names[fc[m]->length-1]));
      fscanf(faulty_combs_file, " %s\n", fc[m]->names[fc[m]->length-1]);
      // printf("%s\n", fc[k]->names[fc[k]->length-1]);
    }
    // printf("\n");
    // printf("k = %d\n", k);
    for(int f=1; f<=k; f++){
      Faults * fv = malloc(sizeof(*fv));
      Comb * comb = first_comb(f, 0);
      do{

        FaultedVar ** v = malloc(f * sizeof(*v));
        for(int j=0; j<f; j++){
          v[j] = malloc(sizeof(*v[j]));
          v[j]->set = set;
          v[j]->name = names[comb[j]];
          v[j]->fault_on_input = false;
        }
        fv->vars = v;
        fv->length = f;

        if(ignore_faulty_scenario(fv, sfc)){
          compute_combined_intermediate_mu(f, length, pfault, mu[i]);
          compute_combined_intermediate_mu(f, length, pfault, mu_max[i]);
          goto skip;
        }
        
        uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));
        fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
        // for(int i=0; i<total_wires+1;i++){
        //   printf("%"PRId64", ", coeffs[i]);
        // }
        // printf("\n");
        compute_combined_intermediate_leakage_proba(coeffs, f, length, total_wires+1, pleak, pfault, epsilon[i], -1);
        compute_combined_intermediate_leakage_proba(coeffs, f, length, total_wires+1, pleak, pfault, epsilon_max[i], coeff_max);
        free(coeffs);

        // gmp_printf("%.10Ff\n", epsilon[i]);

        skip:;
        for(int j=0; j<f; j++){
          free(v[j]);
        }
        free(v);
      }while(incr_comb_in_place(comb, f, length));
      free(comb);
      free(fv);
    }

    uint64_t * coeffs = calloc(c->total_wires+1, sizeof(*coeffs));
    fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
    compute_combined_intermediate_leakage_proba(coeffs, 0, length, total_wires+1, pleak, pfault, epsilon[i], -1);
    compute_combined_intermediate_leakage_proba(coeffs, 0, length, total_wires+1, pleak, pfault, epsilon_max[i], coeff_max);
    free(coeffs);

    // gmp_printf("%.10Ff\n", epsilon[i]);

    for(int k=0; k<size_input_comb; k++){
      free(v_inps[k]->name);
      free(v_inps[k]);
    }
    free(v_inps);
    free_faults_combs(sfc);
  }

  for(int i=0; i<nb_input_combs; i++){
    gmp_printf("%.10Ff\n", epsilon[i]);
  }

  fclose(coeffs_file);
  fclose(faulty_combs_file);
  for(int i=0; i<length; i++){
    free(names[i]);
  }
  free(names);
}