# PCVE_ HANDOFF (P3e): domain equality for transport row_loop.body, row_loop, row

Target not yet established. No ledger, trust row, RSL, contract or shipped source changed. Nothing pushed.

Established (PRVEq_transport_row_P3.lean, PCVE_L006 exit 0, 7.6 s, peak RSS 3.9 GB, swap 0, axioms standard):
* row_loop.body_dom and row_loop_dom: fresh (overflow-OFF text, PCQH ShrAmt prelude) = gate for iter.end <= 16.
* row: fresh = gate with NO domain hypothesis.
No reachable input makes the bodies disagree; ShrAmt is not an extra hypothesis of the proof but is inside the fresh text (it only elaborates through the PCQH prelude), so the result stays tied to the PCQH-C2 hand model until the MIR check.

Why L022..L025 failed: after `cases o` the goal still has `let (o, iter1) := (some d, iter1); match_1 ... (fun d => ...)`; the d in the body is the matcher's bound variable, not the free d, so e_shr (about the free d) never matched. Fix: PCVE.fresh_body_some / gate_body_some reduce each body to its explicit continuation by `rfl` after `rw [hn]`; then the old simp/cases script works unchanged.

Scopes: L001 (dsimp error), L002 (goal print), L003 (reductions), L004 (body_dom), L005 (all), L006 (final file). All one at a time. Remaining: MIR check of ShrAmt; lead to update the family record.
