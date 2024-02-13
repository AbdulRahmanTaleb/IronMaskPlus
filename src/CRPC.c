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

static int generate_input_names(ParsedFile * pf, char *** input_names){
  int input_length = pf->shares * pf->nb_duplications * pf->in->next_val;
  *input_names = malloc(input_length * sizeof(**input_names));
  char ** names = *input_names;

  int idx = 0;
  StrMapElem * elem = pf->in->head;
  while(elem){
    for(int i=0; i<pf->shares; i++){
      for(int j=0; j<pf->nb_duplications; j++){
        names[idx] = malloc(10 * sizeof(*names[idx]));
        sprintf(names[idx], "%s%d_%d", elem->key, i, j);
        idx++;
      }
    }
    elem = elem->next;
  }
  return input_length;
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

void compute_CRPC_coeffs(ParsedFile * pf, int cores, int coeff_max, int k, int t, bool set) {

  if(pf->out->next_val > 1){
    fprintf(stderr, "Cannot verify CRPC for gadgets with more than 1 output.");
    exit(EXIT_FAILURE);
  }

  char ** names;
  int length = generate_names(pf, &names);

  char ** input_names;
  int input_length = generate_input_names(pf, &input_names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;

  if(coeff_max == -1){
    coeff_max = c->length;
  }

  free_circuit(c);

  Faults * fv = malloc(sizeof(*fv));
  fv->length = 1;
  FaultedVar ** v = malloc(1 * sizeof(*v));
  v[0] = malloc(sizeof(*v[0]));
  v[0]->set = set;
  v[0]->name = input_names[0];
  v[0]->fault_on_input = true;
  sscanf(input_names[0], "%*s%d_%d", &v[0]->share, &v[0]->duplicate);
  fv->vars = v;

  Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);
  print_circuit(circuit);
  free(v[0]);
  free(v);
  free(fv);


  for(int inp=0; inp<input_length; inp++){
    free(input_names[inp]);
  }
  free(input_names);
  for(int i=0; i<length; i++){
    // printf("%d %s\n", i, names[i]);
    free(names[i]);
  }
  free(names);
}


void compute_CRPC_val(ParsedFile * pf, int coeff_max, int k, int t, double pleak, double pfault, bool set){
  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;
  free_circuit(c);


  char * filename;
  get_filename(pf, coeff_max, t, k, set, &filename);
  FILE * coeffs_file = fopen(filename, "rb");
  if(!coeffs_file){
    free(filename);
    fprintf(stderr, "file %s not found...", filename);
    exit(EXIT_FAILURE);
  }

  free(filename);

  char * prop = malloc(5 *sizeof(*prop));
  sprintf(prop, "CRPC");
  FaultsCombs * fc = read_faulty_scenarios(pf, k, set, prop);
  free(prop);

  Faults * fv = malloc(sizeof(*fv));
  fv->length = k;

  uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));
  mpf_t res;
  mpf_init(res);

  int cpt = 0;
  int cpt_ignored = 0;
  int remove;
  for(int i=1; i<=k; i++){

    fv->length = i;

    Comb * comb = first_comb(i, 0);
    do{
      remove = 0;
      FaultedVar ** v = malloc(i * sizeof(*v));
      for(int j=0; j<i; j++){
        v[j] = malloc(sizeof(*v[j]));
        v[j]->set = set;
        v[j]->name = names[comb[j]];
      }
      fv->vars = v;

      if(ignore_faulty_scenario(fv, fc)){
        cpt_ignored++;
        goto skip;
      }

      // for(int l=0;l<i;l++){
      //   for(int m=0; m< input_length; m++){
      //     if(strcmp(fv->vars[l]->name, input_names[m]) == 0){
      //       remove++;
      //       break;
      //     }
      //   }
      // }

      fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
      // get_failure_proba(coeffs, total_wires+1, pleak);
      compute_combined_intermediate_leakage_proba(coeffs, i-remove, length - pf->shares * pf->nb_duplications * pf->in->next_val, total_wires+1, pleak, pfault, res, -1);
      cpt++;

      skip:;
      free(v);
    }while(incr_comb_in_place(comb, i, length));
  }

  fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
  // get_failure_proba(coeffs, total_wires+1, pleak);
  compute_combined_intermediate_leakage_proba(coeffs, 0, length - pf->shares * pf->nb_duplications * pf->in->next_val, total_wires+1, pleak, pfault, res, -1);
  
  fclose(coeffs_file);

  gmp_printf("\n\nf(%.2lf, %.2lf) = %.10Ff for a total of %d faulty scenarios\n", pleak, pfault, res, cpt);
  mpf_clear(res);

  // for(int i=0; i<input_length; i++){
  //   free(input_names[i]);
  // }
  // free(input_names);
}