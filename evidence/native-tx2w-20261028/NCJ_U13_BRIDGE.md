# U13 native bridge ledger

OPEN: target not yet established. Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

| Function | Native gate | Lean association | Status / obligation |
|---|---|---|---|
| `finish_query_dot` | pending | pending | OPEN: Two224-byte degree6 polynomials, two alphas and claim from same resume; relation lhs=claim/4 then Horner; invoke U12 on SAME final message/kappa; final dot64 canonical weights, next=22 and actual=rhs; preserve errors and marks(None). |
| `finish_relation` | pending | pending | OPEN: Two224-byte degree6 polynomials, two alphas and claim from same resume; relation lhs=claim/4 then Horner; invoke U12 on SAME final message/kappa; final dot64 canonical weights, next=22 and actual=rhs; preserve errors and marks(None). |
| `finish_relation_round` | pending | pending | OPEN: Two224-byte degree6 polynomials, two alphas and claim from same resume; relation lhs=claim/4 then Horner; invoke U12 on SAME final message/kappa; final dot64 canonical weights, next=22 and actual=rhs; preserve errors and marks(None). |
| `polynomial` | pending | pending | OPEN: Two224-byte degree6 polynomials, two alphas and claim from same resume; relation lhs=claim/4 then Horner; invoke U12 on SAME final message/kappa; final dot64 canonical weights, next=22 and actual=rhs; preserve errors and marks(None). |

## Stage 4 native control results

K037 PASS / K038 FAIL: actual frozen finish_relation_round on SAME224-byte canonical polynomial, canonical alpha and claim, round0/1; two exact field indices0/4, same arbitrary selected source byte, lhs-vs-quarter reply, exact Relation error and no polynomial call on failure; same alpha/bytes and unchanged polynomial reply on success. Field decoder and polynomial are OPEN callee substitutions. This closes only local control routing, not the whole round.

K039 PASS / K040 FAIL: one literal Horner closure update, arbitrary canonical prestate and scalar, arbitrary i<7 on canonical SAME224 bytes; exact operand/read routing and linear sum. Multiplication is an opaque logged reply with LPi_TowerValues.wide_mul; decoding retains the exact lower-field native association qualification. NCJ_HornerInduction.total (L017) supplies canonical induction. Full adopted polynomial port/source association is OPEN.

finish_relation is not given native credit: its observer is Option<fn(Phase)> and rule14 remains binding. No harness was renamed to alter a verdict. No digest or function-pointer value was modeled.

Stage6 K057 PASS / K058 FAIL is one actual final-dot push fragment: arbitrary valid raw prestate/count<64, exact scalar/value and byte-index routing, both raw reply updates and count+1. It uses the same explicit U06/U07 qualifications as the U12 dot fragments. Native same-final-message association and full finish_query_dot call/return remain OPEN.
