#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <inttypes.h>

#include "NI.h"
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

void compute_CRP_coeffs(ParsedFile * pf, int cores, int coeff_max, int k) {

  char ** names;
  int length = generate_names(pf, &names);

  Circuit * c = gen_circuit(pf, pf->glitch, pf->transition, NULL);
  int total_wires = c->total_wires;

  uint64_t ** coeffs = malloc(length * 2 * sizeof(*coeffs));
  for(int i=0; i<length*2; i++){
    coeffs[i] = calloc(c->total_wires+1, sizeof(*coeffs[i]));
  }

  int coeff_max_main_loop = (coeff_max == -1) ? (c->length) :
    (coeff_max > c->length ? c->length : coeff_max);

  if(coeff_max == -1){
    coeff_max = c->length;
  }

  free_circuit(c);

  Faults * fv = malloc(sizeof(*fv));
  fv->length = k;
  assert(k==1);
  FaultedVar * v1 = malloc(sizeof(*v1));
  FaultedVar * v[1] = {v1};
  fv->vars = v;

  for(int i=0; i< length; i++){

    printf("################ Cheking CRP with fault on %s...\n", names[i]);

    for(int s = 0; s<2; s++){

      v1->name = names[i];
      v1->set = s;

      //printf("------%s:\n", v1->set ? "set":"reset");

      Circuit * circuit = gen_circuit(pf, pf->glitch, pf->transition, fv);
      //print_circuit(c);
      DimRedData* dim_red_data = remove_elementary_wires(circuit, false);

      struct callback_data data = {
        .coeffs = coeffs[i*2 + s],
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
        //   printf("%"PRIu64", ", coeffs[i*2 + s][size]); fflush(stdout);
        // }
      }

      // for (int k = coeff_max_main_loop+1; k < total_wires-1; k++) {
      //   printf("%"PRIu64", ", coeffs[i*2 + s][k]);
      // }
      // printf("%"PRIu64" ]\n", coeffs[i*2 + s][circuit->total_wires]);

      free_circuit(c);

    }

    //printf("################\n\n");
    
    free(names[i]);
    
  }

  free(names);

  free(v1);
  free(fv);
}
