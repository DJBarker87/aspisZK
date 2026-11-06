import NKI_InitialInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialTrace
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
def run (public1 : Public) (openings : Openings) (selectors : Selectors) : Result Locals := do

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
  ok ⟨s,nodes,q,q1,q2,q3,q4,q5,first_common,q6,q7,q8,transfer_first,fixed,private_chunk_eight,private_chunk_two,q9,q10,q11,full_initial_selector,rate_initial_selector,full,q12,full_or_rate,initial,q13,note_first,q14,q15,q16,q17,domain,q18,q19,q20,q21,length,q22,q23,q24,initial1,i,q25,q26,q27,initial2,q28,q29,q30,q31,q32,q33,q34,q35,chunk_eight,q36,q37,chunk_two,chunk_eight1,chunk_two1,q38⟩
def Canonical (l : Locals) : Prop :=
 Canon l.nodes ∧
 Canon l.q ∧
 Canon l.q1 ∧
 Canon l.q2 ∧
 Canon l.q3 ∧
 Canon l.q4 ∧
 Canon l.q5 ∧
 Canon l.first_common ∧
 Canon l.q6 ∧
 Canon l.q7 ∧
 Canon l.q8 ∧
 Canon l.transfer_first ∧
 Canon l.fixed ∧
 Canon l.private_chunk_eight ∧
 Canon l.private_chunk_two ∧
 Canon l.q9 ∧
 Canon l.q10 ∧
 Canon l.q11 ∧
 Canon l.full_initial_selector ∧
 Canon l.rate_initial_selector ∧
 JFy_PreparedSteps.Valid l.full ∧
 Canon l.q12 ∧
 JFy_PreparedSteps.Valid l.full_or_rate ∧
 canonical l.initial ∧
 Canon l.q13 ∧
 Canon l.note_first ∧
 Canon l.q14 ∧
 Canon l.q15 ∧
 Canon l.q16 ∧
 Canon l.q17 ∧
 Canon l.domain ∧
 Canon l.q18 ∧
 Canon l.q19 ∧
 Canon l.q20 ∧
 Canon l.q21 ∧
 Canon l.length ∧
 Canon l.q22 ∧
 Canon l.q23 ∧
 Canon l.q24 ∧
 canonical l.initial1 ∧
 Canon l.q25 ∧
 Canon l.q26 ∧
 Canon l.q27 ∧
 canonical l.initial2 ∧
 Canon l.q28 ∧
 Canon l.q29 ∧
 Canon l.q30 ∧
 Canon l.q31 ∧
 Canon l.q32 ∧
 Canon l.q33 ∧
 Canon l.q34 ∧
 Canon l.q35 ∧
 Canon l.chunk_eight ∧
 Canon l.q36 ∧
 Canon l.q37 ∧
 Canon l.chunk_two ∧
 Canon l.chunk_eight1 ∧
 Canon l.chunk_two1 ∧
 Canon l.q38
/-- All actual intermediate domains are returned, for later native cut
instantiation. No scalar, cache or array domain is an extra root premise. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 run p o s ⦃ l=>Canonical l ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 unfold run poseidon2.RATE
 step*
 all_goals first
  | (subst_vars;exact FIx_ScheduleIndices.node_bounds)
  | (unfold Canonical;exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩)
#print axioms source
end AspisR1.NKI_InitialTrace
end
