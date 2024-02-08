#pragma once

#include "circuit.h"
#include "dimensions.h"
#include "utils.h"

void compute_CRP_coeffs(ParsedFile * pf, int cores, int coeff_max, int k);

void compute_CRP_val(ParsedFile * pf, int coeff_max, int k, double pleak, double pfault);