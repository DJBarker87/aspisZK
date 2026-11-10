# PCWN_ handoff (P5e, in progress)

## Item 1: public_bytes library-name lemma (SETTLED, no abbrev)
PRVEq_PB_w3.lean (scope PCWN_L004 exit 0, 21.4 s, peak RSS 2.69 GB, swap 0, standard axioms only, default heartbeats on every lemma and theorem).
The new-library constants (Result.branch, Result.from_residual, Never; Aeneas 0d21a9ec, Convert.lean sha256 e2586558..., attributes omitted) are copied verbatim into PCWN_NewLib.
Finding: the two libraries do not differ only by name. The new library types the residual with `Never`, the gate with `core.convert.Infallible`; both are empty inductives but distinct types, so a literal equality of the two constants is not statable. The proved statements are:
- PCWN_NewLib.from_residual_eq: new from_residual applied to (castR r) = gate from_residual applied to r (castR: the empty-type map).
- PCWN_NewLib.branch_bind: Bind of new branch with F = Bind of gate branch with G, given agreement on the Continue arm and on the Break (Err e) arm.
The nine fresh = gate theorems now use the new constants textually (qualified PCWN_NewLib.), with frontier and public_bytes proved by the pb_chain tactic using branch_bind. The abbrev is removed. No row named.
Budget: item 1 used L001-L003; L004 was the heartbeat-reset recheck (charged to the main batch budget).
