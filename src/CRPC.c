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

void compute_CRPC(ParsedFile * pf, int cores, int coeff_max, int k, int t) {

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

  Faults * fv = malloc(sizeof(*fv));
  fv->length = k;

  uint64_t out_comb_len;
  Comb** out_comb_arr = gen_combinations(&out_comb_len, t, pf->shares - 1);
  printf("len = %d\n", out_comb_len);
  Comb * out_comb = malloc((t * pf->nb_duplications) * sizeof(*out_comb));

  uint64_t** coeffs_out_comb;
  coeffs_out_comb = malloc(out_comb_len * sizeof(*coeffs_out_comb));
  for (unsigned i = 0; i < out_comb_len; i++) {
    coeffs_out_comb[i] = malloc((total_wires + 1) *  sizeof(*coeffs_out_comb[i]));
  }

  VarVector verif_prefix = { .length = t*pf->nb_duplications, 
                             .max_size = t*pf->nb_duplications, 
                             .content = NULL };

  struct callback_data data = { .t = t, .coeffs = NULL, .nb_duplications = pf->nb_duplications };

  mpf_t res;
  mpf_init(res);

  for(int i=1; i<=k; i++){

    fv->length = i;

    Comb * comb = first_comb(i, 0);
    do{

      printf("################ Cheking CRPC with faults on ");
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

      uint64_t * coeffs = calloc(c->total_wires+1, sizeof(*coeffs));
      for (unsigned i = 0; i < out_comb_len; i++) {
        memset(coeffs_out_comb[i], 0, (total_wires + 1) *  sizeof(*coeffs_out_comb[i]));
      }

      Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);
      //print_circuit(circuit);

      for (int size = 0; size <= coeff_max; size++) {

        for (unsigned int l = 0; l < out_comb_len; l++) {
          construct_output_prefix(circuit, pf->out, out_comb_arr[l], out_comb, t);
          verif_prefix.content = out_comb;
          data.coeffs = coeffs_out_comb[l];
          // for(int m=0; m< t*c->nb_duplications; m++){
          //   printf("%d, ", out_comb[m]);
          // }
          // printf("\n");

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

          #define max(a,b) ((a) > (b) ? (a) : (b))
          coeffs[size] = max(coeffs[size], coeffs_out_comb[l][size]);
          //printf("coeff = %lu\n", coeffs_out_comb[l][size]);

        }
      }

      for (int i = coeff_max+1; i <= circuit->total_wires; i++) {
        for (unsigned j = 0; j < out_comb_len; j++) {
          coeffs[i] = max(coeffs[i], coeffs_out_comb[j][i]);
        }
      }

      get_failure_proba(coeffs, total_wires+1, 0.01);
      compute_combined_intermediate_leakage_proba(coeffs, i, length, total_wires+1, 0.01, 0.01, res);

      // for (int k = coeff_max_main_loop+1; k < total_wires-1; k++) {
      //   printf("%"PRIu64", ", coeffs[i*2 + s][k]);
      // }
      // printf("%"PRIu64" ]\n", coeffs[i*2 + s][circuit->total_wires]);

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
  printf("################ Cheking CRPC without faults\n");
  uint64_t * coeffs = calloc(c->total_wires+1, sizeof(*coeffs));
  for (unsigned i = 0; i < out_comb_len; i++) {
    memset(coeffs_out_comb[i], 0, (total_wires + 1) *  sizeof(*coeffs_out_comb[i]));
  }
  Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  for (int size = 0; size <= coeff_max; size++) {

    for (unsigned int l = 0; l < out_comb_len; l++) {
      construct_output_prefix(circuit, pf->out, out_comb_arr[l], out_comb, t);
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

      #define max(a,b) ((a) > (b) ? (a) : (b))
      coeffs[size] = max(coeffs[size], coeffs_out_comb[l][size]);
      //printf("coeff = %lu\n", coeffs_out_comb[l][size]);

    }
  }
  for (int i = coeff_max+1; i <= circuit->total_wires; i++) {
    for (unsigned j = 0; j < out_comb_len; j++) {
      coeffs[i] = max(coeffs[i], coeffs_out_comb[j][i]);
    }
  }
  get_failure_proba(coeffs, total_wires+1, 0.01);
  compute_combined_intermediate_leakage_proba(coeffs, 0, length, total_wires+1, 0.01, 0.01, res);
  free_circuit(circuit);
  free(coeffs);

  gmp_printf("\n\nf(%.2lf, %.2lf) = %.10Ff\n", 0.01, 0.01, res);
  mpf_clear(res);
}
