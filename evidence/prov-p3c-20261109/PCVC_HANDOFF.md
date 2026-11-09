# PCVC_ HANDOFF: phase P3c (tool-encoding bridges for P2g's failure list)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed. Branch codex/pc-prov-p3c-20261109; host workspace /home/dombarker/project-offloads/codex-pc-prov-p3c-20261109/. 47 of 60 Lean scopes (PCVC_L001-L047; L034, L042, L043 timeouts 124; L036 exit 134 at the -M7000 cap), 0 extraction, caps 6G/8G swap 0, 180 s; peak RSS 2.6-3.3 GB except L036.

## Claims established (each theorem in a file whose scope exited 0 and whose #print axioms is propext/Classical.choice/Quot.sound only)
* Generic loop bridge (PRVC_LoopBridge.lean): fresh Aeneas `loop body x` = gate partial_fixpoint def, by loop_le (fixpoint induction on loop), hge (fixpoint induction on the gate def) and antisymmetry. Applied per loop, no stage-1 rfl.
* 31 P2g FAILED definitions proved fresh = gate (PCVC_STATUS.json): Native01 (3 loops + callees), Native02 (4 loops), Native04, 05, 06, 07, 08, 09, 10, 11 (loop defs and wrappers whose fresh closure elaborates), file PRVEq_<M>_P3.lean, attempt in the status record. Class SOURCE_SHAPE.
* WithdrawalCaller validate_common and validate_pool_v1_withdrawal_public_v1 (lead priority): SOURCE_SHAPE, proved (PCVC_L046). The only text difference is the constant path (fresh pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY, spend.VALUE_LIMIT vs gate pool_v1.POOL_V1_LEAF_CAPACITY, VALUE_LIMIT); values equal (1#u64 <<< 20#usize, 1#u32 <<< 30#i32), proved. No input on which they disagree.
* TerminalDecoder digest_is_canonical family: P2f's PRVEq_TD_HP_P3f.lean discharges it (not recompiled here). Option Bool vs Bool is a loop-return encoding (body/loop: refinement through conv; digest_is_canonical and output_lane_v1: plain equalities). Corrected class SOURCE_SHAPE. Retained caveats in PCVC_STATUS.json (P from PCQF_E002; gate module non-frozen per PCXA).

## Not established
79 records open (PCVC_REMAINING.json). Causes: core.array.from_fn is an axiom in the original emission (hand model, PCVC_HAND_MODELS.json; fresh declarations depending on it do not elaborate and cascade); constant-binding lemma and hoisted-constant parameter not done; Native13 and Native14 fresh sections do not elaborate in 180 s even without any theorem (L043 base only): shape retired; PoseidonPreparedSum3Source gate namespace mismatch not resolved; 5 CONFIG_MISMATCH need OFF emissions (PCVC_NEED_EXTRACTION.json); TerminalDecoder pair_terminal/pair_tree_profile EXTERNAL_P not restated; r0.transport.order not examined.

## Failed shapes
L036: generic destructure-every-product alternative in prv_peel: 177 s, 7.2 GB abort; replaced by simp lemma uncurry_proj. L034/L042/L043: Native13 timeouts. Default `rfl` inside prv_peel (heartbeat timeouts on array terms) replaced by with_reducible rfl.
