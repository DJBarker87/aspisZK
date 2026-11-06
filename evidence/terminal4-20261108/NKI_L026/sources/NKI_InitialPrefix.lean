import NDO_JFy_Schedule
import NJL_AbsorptionInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialPrefix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
structure Tail where
 initial : Array field.QM31 16#usize
 low : field.QM31
 fixed : field.QM31
 two : field.QM31
 eight : field.QM31
 nodes : field.QM31
def run (public1 : Public) (openings : Openings) (selectors : Selectors) : Result Tail := do
  let s ←
    lift (Array.to_slice
      (Array.make 2#usize [
        ({ start := 4#usize, «end» := 25#usize } : core.ops.range.Range
        Std.Usize), ({ start := 33#usize, «end» := 57#usize } :
        core.ops.range.Range Std.Usize)
        ]))
  let nodes ← pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  let q ← Array.index_usize selectors.high 0#usize
  let q1 ← Array.index_usize selectors.high 1#usize
  let q2 ← field.QM31.add q q1
  let q3 ← Array.index_usize selectors.high 25#usize
  let q4 ← field.QM31.add q2 q3
  let q5 ← Array.index_usize selectors.high 30#usize
  let first_common ← field.QM31.add q4 q5
  let q6 ← Array.index_usize selectors.high 27#usize
  let q7 ← Array.index_usize selectors.high 28#usize
  let q8 ← Array.index_usize selectors.high 29#usize
  let (transfer_first, fixed, private_chunk_eight, private_chunk_two) ←
    pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
      public1.variant q6 q7 q8
  let q9 ← Array.index_usize selectors.low 0#usize
  let q10 ← field.QM31.add first_common transfer_first
  let q11 ← field.QM31.add q10 fixed
  let full_initial_selector ← field.QM31.mul q9 q11
  let rate_initial_selector ← field.QM31.mul q9 nodes
  let full ← field.PreparedQm31Multiplier.new full_initial_selector
  let q12 ← field.QM31.add full_initial_selector rate_initial_selector
  let full_or_rate ← field.PreparedQm31Multiplier.new q12
  let initial ←
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO (full_or_rate, openings, full)
  let q13 ← field.QM31.add q1 q5
  let note_first ← field.QM31.add q13 transfer_first
  let q14 ← field.QM31.mul_m31 q spend.DOMAIN_OWNER_KEY
  let q15 ← field.QM31.mul_m31 note_first spend.DOMAIN_NOTE
  let q16 ← field.QM31.add q14 q15
  let q17 ← field.QM31.mul_m31 q3 spend.DOMAIN_NULLIFIER
  let domain ← field.QM31.add q16 q17
  let q18 ← field.QM31.mul_m31 q 8#u32
  let q19 ← field.QM31.mul_m31 note_first 18#u32
  let q20 ← field.QM31.add q18 q19
  let q21 ← field.QM31.mul_m31 q3 16#u32
  let length ← field.QM31.add q20 q21
  let q22 ← Array.index_usize initial poseidon2.RATE
  let q23 ← field.QM31.mul q9 domain
  let q24 ← field.QM31.sub q22 q23
  let initial1 ← Array.update initial poseidon2.RATE q24
  let i ← poseidon2.RATE + 1#usize
  let q25 ← Array.index_usize initial1 i
  let q26 ← field.QM31.mul q9 length
  let q27 ← field.QM31.sub q25 q26
  let initial2 ← Array.update initial1 i q27
  let q28 ← field.QM31.add q q1
  let q29 ← Array.index_usize selectors.high 2#usize
  let q30 ← field.QM31.add q28 q29
  let q31 ← field.QM31.add q30 q3
  let q32 ← Array.index_usize selectors.high 26#usize
  let q33 ← field.QM31.add q31 q32
  let q34 ← field.QM31.add q33 q5
  let q35 ← Array.index_usize selectors.high 31#usize
  let chunk_eight ← field.QM31.add q34 q35
  let q36 ← Array.index_usize selectors.high 3#usize
  let q37 ← Array.index_usize selectors.high 32#usize
  let chunk_two ← field.QM31.add q36 q37
  let chunk_eight1 ← field.QM31.add chunk_eight private_chunk_eight
  let chunk_two1 ← field.QM31.add chunk_two private_chunk_two
  let q38 ← Array.index_usize selectors.low 12#usize
  ok ⟨initial2,q38,fixed,chunk_two1,chunk_eight1,nodes⟩
#print run
end AspisR1.NKI_InitialPrefix
end
