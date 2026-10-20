# Gamma caller, end-around model and candidate scalar quotient

PROVED for the unchanged frozen gamma caller under explicit low-digit/add-small helper refinement: successful execution supplies the actual helper successes and final decoder input. That input equals the retained gammaDigits model, is canonical, and has positional rank `(rank(block) mod (P^8-1))+1`, strictly between zero and P^8. The checked quotient increment uses the existing quotient≤256 theorem. Existing end-around and rank mathematics is reused.

The indexed low-digit candidate's returned scalar quotient now equals `rank(block)/P^8`. This is derived from the already proved complete quotient-array value and a symbolic low-word modulus identity. The prior ordinary sampler proof discarded that scalar and did not close this gamma obligation.

The complete add-small helper instance, field decoding, candidate equivalence/adoption and transcript/runtime source joins remain OPEN. This is not a claim that current production gamma sampling or full 100-bit soundness is proved. No production source changed. Arithmetic helpers are explicit function parameters; no opaque template axiom is imported by the compiled owners.

Charon/Aeneas and five focused Lean targets passed on the NUC under explicit caps with zero swap; Lean uses -M4400. Three theorem audits contain standard axioms only. Exact source/import/tool/object pins, commands, time/RSS and failed elaboration diagnostics are retained without binaries. The recursive-mod simplifier failure was replaced by the named single-step Nat.mul_add_mod_self_right identity, without raising recursion or resource limits.
