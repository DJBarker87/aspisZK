#!/usr/bin/env python3
"""Fixed exact C1 does not reduce false-claim cancellation to degree two.

This is an exact F31 relation-claim control, not a selected semantic/payment
execution or a small-field extrapolation. All coefficients are fixed before
gamma. Zero received words, zero OOD answers and final zero are used.
"""
import json


P = 31


def eval_poly(coeff, x):
    value = 0
    for c in reversed(coeff):
        value = (value * x + c) % P
    return value


def main():
    # E(X)=product_{r=1}^{25}(X-r); its 26 coefficients occupy C1 lanes0..25.
    coeff = [1]
    for root in range(1, 26):
        out = [0] * (len(coeff) + 1)
        for i, c in enumerate(coeff):
            out[i] = (out[i] - root * c) % P
            out[i + 1] = (out[i + 1] + c) % P
        coeff = out
    assert len(coeff) == 26 and coeff[-1] == 1
    roots = [gamma for gamma in range(1, P) if eval_poly(coeff, gamma) == 0]
    assert roots == list(range(1, 26))
    zero_priors = 0
    for gamma in range(1, P):
        value = eval_poly(coeff, gamma)
        scaled = pow(pow(gamma, 26, P), -1, P) * value % P
        assert (scaled == 0) == (value == 0)
        for kappa in range(1, P):
            if kappa * value % P == 0:
                zero_priors += 1
    assert zero_priors == 25 * 30
    # No degree≤2 polynomial can equal the scaled false-C1 claim on every
    # nonzero challenge: exhaust all31^3 quadratics as an independent check.
    scaled_values = [pow(pow(g, 26, P), -1, P) * eval_poly(coeff, g) % P
                     for g in range(1, P)]
    quadratic_fits = 0
    for a in range(P):
        for b in range(P):
            for c in range(P):
                if all((a + b*g + c*g*g) % P == v
                       for g, v in zip(range(1, P), scaled_values)):
                    quadratic_fits += 1
    assert quadratic_fits == 0
    print(json.dumps({
        "scope": "exact fixed-prefix relation-claim control; not payment acceptance",
        "field": P, "C1_is_exact_zero_codeword": True,
        "C2_is_exact_zero_codeword": True, "C1_error_degree": 25,
        "nonzero_gamma_roots": roots,
        "gamma_kappa_states_checked": 30*30,
        "zero_shifted_priors": zero_priors,
        "quadratics_exhausted": P**3,
        "quadratic_fits_to_scaled_C1_error": quadratic_fits,
        "new_global_security_bound": None,
    }, indent=2))


if __name__ == "__main__":
    main()
