# Two round-polynomial comparisons

Root proof design, 2026-10-13. This records the finite bad-set route to be
instantiated after the repeated-lift extraction. It is not a compiled R1
binding or Fiat-Shamir theorem.

Fix the literal committed word tuple W. Its joint candidate list Lambda(W)
is fixed before gamma and has at most 100 entries. For each candidate t,
let q_t be its gamma-batched coefficient vector and let w be the public
weighted vector, fixed after kappa. Define the true degree-at-most-six
first-round polynomial R0_t from q_t and w using the source's `round`.

At the first fold challenge alpha0, fold both q_t and its dual weights.
The resulting true second-round polynomial R1_t also has degree at most
six. It is fixed before alpha1. The prover's announced P1 and intermediate
root are absorbed before alpha1.

The matching/extraction route outside the decoder bad sets gives a candidate
t for which the final message equals fold(fold(q_t,alpha0),alpha1).
The final pairing check therefore implies P1(alpha1)=R1_t(alpha1).
Union over all 100 candidates: the roots of nonzero P1-R1_t cost at most
600 alpha1 values. Outside this set, P1=R1_t as polynomials.

The source checks P1[0]+P1[4] = P0(alpha0)/4. The true round boundary identity
is R1_t[0]+R1_t[4] = R0_t(alpha0)/4. Since four is nonzero, this gives
P0(alpha0)=R0_t(alpha0). P0 was absorbed before alpha0. A second union over
the 100 degree-six differences P0-R0_t costs at most 600 alpha0 values.
Outside it P0=R0_t, and its initial boundary check gives the claimed weighted
pairing for q_t. The direct kappa/gamma coefficient comparison in
`SECURITY-PATH.md` then supplies all six per-lane functional claims.

The order matters: the alpha0 bad set is defined from W, gamma, kappa and P0,
without knowing alpha1. The alpha1 bad set is defined after alpha0, from the
same fixed joint list, folded candidates and P1. No selected decoded message
is allowed to depend on the challenge without taking the union over this
fixed list. Candidate extraction must explicitly identify the extracted
message with the batch of a member of Lambda(W).

The generic finite-family root bounds (100 times 6, and 600 times 28) are
compiled in `lean/FunctionalBatch.lean`. The proposed fold-row caps are
therefore 9396508281246 + 600 each, sampled in WideExact. The earlier first
and second round source boundary identities, encoder/fold commutation,
matching extraction, and full FS row instantiation remain to be connected.
No work or grinding factor is used in these caps.

## Focused formal progress

`lean/RoundPairing.lean` now proves the generic degree-six, evaluation and
coefficient-boundary identities for the exact quarter-scaled primal/dual
formulas, including the `[0,3,2,1]` source permutation and Horner orders.
`lean/TwoRoundComparison.lean` proves both finite-family 600-root bounds and
the deterministic backward comparison using one candidate in the fixed
family. Its final-evaluation, boundary and candidate premises remain explicit.
Both compile on the NUC with only standard axioms; receipts are in
`evidence/lean-round-pairing-20261013/` and
`evidence/lean-two-round-comparison-20261013/`.

This replaces those generic algebraic steps with checked lemmas. It does
not supply the extracted candidate, the runtime-to-formula correspondence,
prefix causality, or the Fiat--Shamir instantiation.

`lean/TwoRoundPairing.lean` now composes those lemmas with the specified
primal and quarter-scaled dual folds. It derives the true boundaries and
final evaluation identity internally, and recovers the original pairing
from a final vector extracted by two folds. Extraction itself remains a
premise. `lean/JointFunctionalBinding.lean` proves the subsequent gamma/kappa
comparison for six linear functionals on 29-entry tuples, including the
actual discrepancy-polynomial construction, coefficient identities and
16,800/600 bounds. The tuple family is an explicit input; identifying it
with the concrete committed-word list is the remaining instantiation.
