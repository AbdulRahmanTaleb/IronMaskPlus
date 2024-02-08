#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <inttypes.h>
#include <gmp.h>

#include "CRP.h"
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
  bool dimension_reduction;
  Circuit* init_circuit;
  int* new_to_old_mapping;
};


static int generate_names(ParsedFile * pf, char *** names_ptr){
  int length = pf->nb_duplications * pf->shares * pf->in->next_val + pf->randoms->next_val + pf->eqs->size;
  // we don't need to consider faults on output shares
  length = length - pf->nb_duplications * pf->shares * pf->out->next_val;

  char ** outputs = malloc(pf->nb_duplications * pf->shares * pf->out->next_val * sizeof(*outputs));
  int idx = 0;
  StrMapElem * o = pf->out->head;
  while(o){
    for(int i=0; i< pf->shares; i++){
      for(int j=0; j< pf->nb_duplications; j++){
        outputs[idx] = malloc(10 * sizeof(*outputs[idx]));
        sprintf(outputs[idx], "%s%d_%d", o->key, i, j);
        idx++;
      }
    }
    o = o->next;
  }
  

  *names_ptr = malloc(length * sizeof(*names_ptr));
  char ** names = *names_ptr;

  idx = 0;
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

  elem = pf->randoms->head;
  while(elem){
    names[idx] = strdup(elem->key);
    idx++;
    elem = elem->next;
  }

  EqListElem * elem_eq = pf->eqs->head;
  while(elem_eq){
    bool out = false;
    for(int i=0; i< pf->nb_duplications * pf->shares * pf->out->next_val; i++){
      if(strcmp(elem_eq->dst, outputs[i]) == 0){
        out = true;
        break;
      }
    }
    if(!out){
      names[idx] = strdup(elem_eq->dst);
      idx++;
    }
    elem_eq = elem_eq->next;
  }

  for(int i=0; i<pf->nb_duplications * pf->shares * pf->out->next_val; i++){
    free(outputs[i]);
  }
  free(outputs);

  return length;
}

static void update_coeffs(const Circuit* c, Comb* comb, int comb_len, SecretDep* secret_deps,
                          void* data_void) {
  struct callback_data* data = (struct callback_data*) data_void;
  (void) secret_deps;
  uint64_t* coeffs = data->coeffs;

  /* printf("[ "); */
  /* for (int i = 0; i < comb_len; i++) printf("%d ", comb[i]); */
  /* printf("]\n"); */

  update_coeff_c_single(c, coeffs, comb, comb_len);
}

static void get_filename(ParsedFile * pf, int coeff_max, int k, char **name){
  *name = malloc(strlen(pf->filename) + 50);
  sprintf(*name, "%s_k%d_c%d.CRP_coeffs", pf->filename, k, coeff_max);
}


void compute_CRP_coeffs(ParsedFile * pf, int cores, int coeff_max, int k) {

  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;

  int coeff_max_main_loop = (coeff_max == -1) ? (c->length) :
    (coeff_max > c->length ? c->length : coeff_max);

  if(coeff_max == -1){
    coeff_max = c->length;
  }

  free_circuit(c);

  Faults * fv = malloc(sizeof(*fv));
  fv->length = k;

  char * filename;
  get_filename(pf, coeff_max, k, &filename);
  FILE * coeffs_file = fopen(filename, "wb");
  free(filename);

  for(int i=1; i<=k; i++){

    fv->length = i;

    Comb * comb = first_comb(i, 0);
    do{

      printf("################ Checking CRP with faults on ");
      for(int j=0; j<i; j++){
        printf("%s, ", names[comb[j]]);
      }
      printf("...\n");

      FaultedVar ** v = malloc(i * sizeof(*v));

      for(int j=0; j<i; j++){
        v[j] = malloc(sizeof(*v[j]));
        v[j]->set = true;
        v[j]->name = names[comb[j]];
      }

      fv->vars = v;

      uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));
      Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);
      // print_circuit(c);
      DimRedData* dim_red_data = remove_elementary_wires(circuit, false);

      struct callback_data data = {
        .coeffs = coeffs,
      };

      // Computing coefficients
      // printf("f(p) = [ "); fflush(stdout);
      for (int size = 0; size <= coeff_max_main_loop; size++) {

        find_all_failures(circuit,
                          cores,
                          -1,    // t_in
                          NULL,  // prefix
                          size,  // comb_len
                          coeff_max,  // max_len
                          dim_red_data,
                          true, // has_random
                          NULL,  // first_comb
                          false,  // include_outputs
                          0,     // shares_to_ignore
                          false, // PINI
                          NULL,
                          update_coeffs,
                          (void*)&data);

        // A failure of size 0 is not possible. However, we still want to
        // iterate in the loop with |size| = 0 to generate the tuples with
        // only elementary shares (which, because of the dimension
        // reduction, are never generated otherwise).
        // if (size > 0) {
        //   printf("%"PRIu64", ", coeffs[size]); fflush(stdout);
        // }
      }

      fwrite(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
      free_circuit(circuit);
      free(coeffs);

    }while(incr_comb_in_place(comb, i, length));

    free(comb);
  }

  for(int i=0; i<length; i++){
    free(names[i]);
  }
  free(names);
  free(fv);

  // add non faulty circuit
  uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));
  Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  // print_circuit(c);
  DimRedData* dim_red_data = remove_elementary_wires(circuit, false);
  struct callback_data data = {
    .coeffs = coeffs,
  };

  // Computing coefficients
  printf("################ Cheking CRP without faults\n");
  for (int size = 0; size <= coeff_max_main_loop; size++) {

    find_all_failures(circuit,
                      cores,
                      -1,    // t_in
                      NULL,  // prefix
                      size,  // comb_len
                      coeff_max,  // max_len
                      dim_red_data,
                      true, // has_random
                      NULL,  // first_comb
                      false,  // include_outputs
                      0,     // shares_to_ignore
                      false, // PINI
                      NULL,
                      update_coeffs,
                      (void*)&data);
  }
  fwrite(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
  free_circuit(circuit);
  free(coeffs);

  fclose(coeffs_file);
}

void compute_CRP_val(ParsedFile * pf, int coeff_max, int k, double pleak, double pfault){
  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;
  free_circuit(c);


  char * filename;
  get_filename(pf, coeff_max, k, &filename);
  FILE * coeffs_file = fopen(filename, "rb");
  if(!coeffs_file){
    free(filename);
    fprintf(stderr, "file %s not found...", filename);
    exit(EXIT_FAILURE);
  }
  free(filename);

  uint64_t * coeffs = calloc(total_wires+1, sizeof(*coeffs));
  mpf_t res;
  mpf_init(res);

  int cpt = 0;
  for(int i=1; i<=k; i++){

    Comb * comb = first_comb(i, 0);
    do{

      fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
      // get_failure_proba(coeffs, total_wires+1, pleak);
      compute_combined_intermediate_leakage_proba(coeffs, i, length, total_wires+1, pleak, pfault, res);
      cpt++;
    }while(incr_comb_in_place(comb, i, length));
  }

  fread(coeffs, sizeof(*coeffs), total_wires+1, coeffs_file);
  // get_failure_proba(coeffs, total_wires+1, pleak);
  compute_combined_intermediate_leakage_proba(coeffs, 0, length, total_wires+1, pleak, pfault, res);
  
  fclose(coeffs_file);

  gmp_printf("\n\nf(%.2lf, %.2lf) = %.10Ff for a total of %d faulty scenarios\n", pleak, pfault, res, cpt);
  mpf_clear(res);
}