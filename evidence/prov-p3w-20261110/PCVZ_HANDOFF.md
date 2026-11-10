# PCVZ_ HANDOFF: phase P3w (Q.raw, Dot.finish, update_residue_row_loop1)

Target not yet established. Frozen 4bb3b3f; fresh emissions are the P1n ones (no new extraction). Branch codex/pc-prov-p3w-20261110, host workspace /home/dombarker/project-offloads/codex-pc-prov-p3w-20261110/.

Claims (all exit-0 scopes, standard axioms only, see PCVZ_STATUS.json and PCVZ_SCOPES.json):
- Q.raw: fresh = gate as functions, in AspisR1CanonicalQRawUnified.Funs (L006) and FIo_QRawFuns (L007). Shape: prove Array.map of a pure callback equals the explicit mapped array (generic lemma map_pure), index into it commutes with the map (idx_mapArr), index into a literal array reduces (idx_make4_k), then simp only over the 50-step chain and a pointwise closure equality. No numeral is evaluated.
- Dot.finish: fresh = gate (L009). Effectful callback (reduce may fail), so map4_mon does a 9-leaf case split on the four reduce results; totality of reduce is not used.
- update_residue_row_loop1 and .body: the gate and the frozen emission return different types from the loop (gate drops the iterator from the done payload). Equality is ill-typed, so the proved statement is a refinement: gate = fresh with the done payload projected to snd (body_proj), and for the loop (loop_proj), via a generic loop-with-projected-result lemma (loop_map). Unconditional. Class: loop-return refinement.

Not claimed: no row table entry changes (125 rows touch the cluster, each has at least 3 further open modules, PCVZ_ROWS.json); gate-only closure helpers have no frozen counterpart; update_residue_row, BatchedWeights.push, EbyKDot.finish stay OPEN.

Differences found: none of value. Encoding differences only (31#i32 vs 31#u32, rfl; loop return type).
Retained: trust rows HM-D (Array.map model) and HM-B (slice iterator next) used, none added.
Ran: 20 Lean scopes (10 exit 0), 0 extraction, each 1 to 2.4 s wall, peak RSS about 2.6 GB, swap 0.
Next: recompute the row/module roll-up with the lead's ruling on gate-only helpers; prove the callers of loop1 against loop_proj.
