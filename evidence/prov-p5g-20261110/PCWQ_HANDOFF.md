# PCWQ_ handoff (job pc-prov-p5g, phase P5g, WAdm route 1)

Target not yet established. No shipped source, ledger row, trust row, RSL or contract changed; no trust row proposed; nothing pushed or merged.
Frozen 4bb3b3f (Pool b936275 checked, no op16 counterpart). Objects: L187 replay closure by reference. Lean scopes 12 of 20 (peak RSS 5.3 GB of the 8 GB cap, longest wall 16.5 s), extraction scopes 3 of 8 (peak 0.6 GB, longest 78.5 s), one at a time, swap 0, no cap or timeout raised.

## Result
Counterpart of the 24 RPz7_WAdm_Fissioned_Funs definitions: the frozen op16 writer path `aspis_r1_cost_probe::verifier::checkpoint` (crates/aspis-r1-cost-probe/src/verifier.rs:326-341) with `put` (324) and `put_k` (325), reached from programs/r1-cost-probe/src/lib.rs:42 first -> verifier::tx1 -> candidate.rs:288. Map: PCWQ_MAP.json.
Fresh emission: PCWQ_E003 (original Aeneas 959659a6, ON, cargo --jobs 4, identity by class receipt PCWE_E003). Equality file: PRVEq_RPz7_WAdm_Fissioned_Funs_q1.lean (receipt PCWQ_L011, exit 0, standard axioms on every theorem, no placeholder proofs, heartbeats 200000). Types: PRVEq_RPz7_WAdm_Fissioned_Types_q2.lean (PCWQ_L012, exit 0).

Main theorem `WAdm_Fissioned.PRVQ.checkpoint_eq`: for the S2 / next = 10 / 64-weight domain the frozen checkpoint (the external `<&Vec<T> as IntoIterator>::into_iter` as a parameter with a satisfiable premise) equals `WAdm_fields` then `WAdm_checkpoint`. Supporting: loop closed forms (G_*, F_*), per-loop equalities (E_loop*, E_body*), continuation wrappers (K_*), cs_S2 (frozen checkpoint_size S2 = 1768).

Per-definition classes (PCWQ_STATUS.json): EQUALITY_PROVED 1 (WAdm_putK), GATE_ONLY_HELPER 8 (the seven wrappers and WAdm_fields), DEPENDS_ON_LIBRARY_TRUST 15 (the seven loop/body pairs and WAdm_checkpoint). None OPEN. Dependencies named per definition: HM-D (array IntoIter), HM-B (slice Iter), `<&Vec as IntoIterator>::into_iter` (no model; row left to the lead), WideExact::to_le_bytes (Aspis function bound by name to the gate hand model).

## Difference at the matching configuration
None that is not an encoding difference. Encoding differences, all proved: slice-iterator loops over `&p.roots`/`&a.weights` against by-value loops; nested point loop against the flat four-QM31 loop. Domain note (not a mismatch): the gate hard-codes S2, 10 and 64 weights; the frozen function is general, so the equality is a specialisation (PCWQ_REMAINING R4).

## Remaining
PCWQ_REMAINING.json: R1 WideExact::to_le_bytes fresh body versus rawBytes; R2 HM-D/HM-B row coverage; R3 the unmodelled &Vec into_iter; R4 the domain question; R5 the composed nested type isomorphism.

## Re-run
`bash run_ext.sh PCWQ_E00n` (spec from PCWQ_mkspec.py), `python3 -B PCWQ_assemble.py PRVEq_RPz7_WAdm_Fissioned_Funs_q1.lean`, `bash run_scope.sh PCWQ_L0nn PRVEq_RPz7_WAdm_Fissioned_Funs_q1`. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p5g-20261110/ (nothing running). Receipts: PCWQ_E00n/, PCWQ_L0nn/receipt.json, PCWQ_ATTEMPTS.jsonl, PCWQ_TRANSPORT.jsonl.

Target not yet established
