import RPv_FIx_ScheduleModel
import RPv_FIx_ScheduleIndices
import RPv_FIx_InitialWrites
import RPv_FIx_InitialArray
import RPv_FIx_AbsorptionArray
import RPv_FIx_ArrayMeaning
import RPv_FIw_ScalarArithmetic
import RPu_FIw_WordValue
import RPv_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ScheduleValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIx_ScheduleModel (high low)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem value (public1 : Public) (openings : Openings) (selectors : Selectors)
    (out1 out2 : Array NQ 16#usize)
    (hz : canonical openings.z) (hh : canonical selectors.high) (hl : canonical selectors.low)
    (run : pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
      public1 openings selectors=ok (out1,out2)) :
    canonical out1 ∧ canonical out2 ∧
      decoded out1=FIx_ScheduleModel.initial public1.variant selectors openings ∧
      decoded out2=FIx_ScheduleModel.absorption public1.variant selectors openings := by
  unfold pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption at run
  obtain ⟨s,h_s,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨nodes,h_nodes,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q,h_q,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q1,h_q1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q2,h_q2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q3,h_q3,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q4,h_q4,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q5,h_q5,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨first_common,h_first_common,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q6,h_q6,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q7,h_q7,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q8,h_q8,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨⟨transfer_first, fixed, private_chunk_eight, private_chunk_two⟩,h_variant,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q9,h_q9,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q10,h_q10,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q11,h_q11,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨full_initial_selector,h_full_initial_selector,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨rate_initial_selector,h_rate_initial_selector,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨full,h_full,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q12,h_q12,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨full_or_rate,h_full_or_rate,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨initial,h_initial,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q13,h_q13,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨note_first,h_note_first,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q14,h_q14,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q15,h_q15,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q16,h_q16,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q17,h_q17,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨domain,h_domain,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q18,h_q18,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q19,h_q19,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q20,h_q20,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q21,h_q21,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨length,h_length,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q22,h_q22,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q23,h_q23,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q24,h_q24,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨initial1,h_initial1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨i,h_i,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q25,h_q25,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q26,h_q26,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q27,h_q27,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨initial2,h_initial2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q28,h_q28,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q29,h_q29,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q30,h_q30,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q31,h_q31,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q32,h_q32,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q33,h_q33,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q34,h_q34,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q35,h_q35,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨chunk_eight,h_chunk_eight,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q36,h_q36,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q37,h_q37,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨chunk_two,h_chunk_two,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨chunk_eight1,h_chunk_eight1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨chunk_two1,h_chunk_two1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q38,h_q38,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨absorption,h_absorption,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
  have s_same : s=FIx_ScheduleModel.nodeRanges  := (Result.ok.inj h_s).symm
  rw [s_same] at h_nodes
  have v_nodes := FIx_HighSum.value selectors FIx_ScheduleModel.nodeRanges nodes FIx_ScheduleIndices.node_bounds hh h_nodes
  have cv_nodes := v_nodes.1
  have vv_nodes : decode nodes=FIx_ScheduleModel.nodes selectors := v_nodes.2
  have cv_q := FIv_NativeArray.canonical selectors.high 0#usize q hh h_q
  have vv_q : decode q=high selectors (0#usize).val := (FIv_NativeArray.read selectors.high 0#usize q h_q).symm
  have cv_q1 := FIv_NativeArray.canonical selectors.high 1#usize q1 hh h_q1
  have vv_q1 : decode q1=high selectors (1#usize).val := (FIv_NativeArray.read selectors.high 1#usize q1 h_q1).symm
  have v_q2 := FIv_NativeValue.add q q1 q2 cv_q cv_q1 h_q2
  have cv_q2 := v_q2.1
  have vv_q2 := v_q2.2
  have cv_q3 := FIv_NativeArray.canonical selectors.high 25#usize q3 hh h_q3
  have vv_q3 : decode q3=high selectors (25#usize).val := (FIv_NativeArray.read selectors.high 25#usize q3 h_q3).symm
  have v_q4 := FIv_NativeValue.add q2 q3 q4 cv_q2 cv_q3 h_q4
  have cv_q4 := v_q4.1
  have vv_q4 := v_q4.2
  have cv_q5 := FIv_NativeArray.canonical selectors.high 30#usize q5 hh h_q5
  have vv_q5 : decode q5=high selectors (30#usize).val := (FIv_NativeArray.read selectors.high 30#usize q5 h_q5).symm
  have v_first_common := FIv_NativeValue.add q4 q5 first_common cv_q4 cv_q5 h_first_common
  have cv_first_common := v_first_common.1
  have vv_first_common := v_first_common.2
  have cv_q6 := FIv_NativeArray.canonical selectors.high 27#usize q6 hh h_q6
  have vv_q6 : decode q6=high selectors (27#usize).val := (FIv_NativeArray.read selectors.high 27#usize q6 h_q6).symm
  have cv_q7 := FIv_NativeArray.canonical selectors.high 28#usize q7 hh h_q7
  have vv_q7 : decode q7=high selectors (28#usize).val := (FIv_NativeArray.read selectors.high 28#usize q7 h_q7).symm
  have cv_q8 := FIv_NativeArray.canonical selectors.high 29#usize q8 hh h_q8
  have vv_q8 : decode q8=high selectors (29#usize).val := (FIv_NativeArray.read selectors.high 29#usize q8 h_q8).symm
  obtain ⟨cv_transfer_first,cv_fixed,cv_private_chunk_eight,cv_private_chunk_two,v_variant⟩ :=
    FIx_InitialVariant.value public1.variant q6 q7 q8 (transfer_first,fixed,private_chunk_eight,private_chunk_two) cv_q6 cv_q7 cv_q8 h_variant
  have vv_transfer_first := congrArg (fun t : K × K × K × K=>t.1) v_variant
  dsimp only at vv_transfer_first
  have vv_fixed := congrArg (fun t : K × K × K × K=>t.2.1) v_variant
  dsimp only at vv_fixed
  have vv_private_chunk_eight := congrArg (fun t : K × K × K × K=>t.2.2.1) v_variant
  dsimp only at vv_private_chunk_eight
  have vv_private_chunk_two := congrArg (fun t : K × K × K × K=>t.2.2.2) v_variant
  dsimp only at vv_private_chunk_two
  have cv_q9 := FIv_NativeArray.canonical selectors.low 0#usize q9 hl h_q9
  have vv_q9 : decode q9=low selectors (0#usize).val := (FIv_NativeArray.read selectors.low 0#usize q9 h_q9).symm
  have v_q10 := FIv_NativeValue.add first_common transfer_first q10 cv_first_common cv_transfer_first h_q10
  have cv_q10 := v_q10.1
  have vv_q10 := v_q10.2
  have v_q11 := FIv_NativeValue.add q10 fixed q11 cv_q10 cv_fixed h_q11
  have cv_q11 := v_q11.1
  have vv_q11 := v_q11.2
  have v_full_initial_selector := FIv_NativeValue.mul q9 q11 full_initial_selector cv_q9 cv_q11 h_full_initial_selector
  have cv_full_initial_selector := v_full_initial_selector.1
  have vv_full_initial_selector := v_full_initial_selector.2
  have v_rate_initial_selector := FIv_NativeValue.mul q9 nodes rate_initial_selector cv_q9 cv_nodes h_rate_initial_selector
  have cv_rate_initial_selector := v_rate_initial_selector.1
  have vv_rate_initial_selector := v_rate_initial_selector.2
  have valid_full := FIv_PreparedNew.valid full_initial_selector full cv_full_initial_selector h_full
  have v_q12 := FIv_NativeValue.add full_initial_selector rate_initial_selector q12 cv_full_initial_selector cv_rate_initial_selector h_q12
  have cv_q12 := v_q12.1
  have vv_q12 := v_q12.2
  have valid_full_or_rate := FIv_PreparedNew.valid q12 full_or_rate cv_q12 h_full_or_rate
  have v_initial := FIx_InitialArray.value q12 full_initial_selector full_or_rate full openings initial
    cv_q12 cv_full_initial_selector valid_full_or_rate valid_full hz h_initial
  have cv_initial := v_initial.1
  have vv_initial := FIx_ArrayMeaning.decoded_of_map initial _ v_initial.2
  have v_q13 := FIv_NativeValue.add q1 q5 q13 cv_q1 cv_q5 h_q13
  have cv_q13 := v_q13.1
  have vv_q13 := v_q13.2
  have v_note_first := FIv_NativeValue.add q13 transfer_first note_first cv_q13 cv_transfer_first h_note_first
  have cv_note_first := v_note_first.1
  have vv_note_first := v_note_first.2
  have v_q14 := FIw_ScalarArithmetic.mul q q14 spend.DOMAIN_OWNER_KEY h_q14
  have cv_q14 := v_q14.1
  have vv_q14 := v_q14.2
  have v_q15 := FIw_ScalarArithmetic.mul note_first q15 spend.DOMAIN_NOTE h_q15
  have cv_q15 := v_q15.1
  have vv_q15 := v_q15.2
  have v_q16 := FIv_NativeValue.add q14 q15 q16 cv_q14 cv_q15 h_q16
  have cv_q16 := v_q16.1
  have vv_q16 := v_q16.2
  have v_q17 := FIw_ScalarArithmetic.mul q3 q17 spend.DOMAIN_NULLIFIER h_q17
  have cv_q17 := v_q17.1
  have vv_q17 := v_q17.2
  have v_domain := FIv_NativeValue.add q16 q17 domain cv_q16 cv_q17 h_domain
  have cv_domain := v_domain.1
  have vv_domain := v_domain.2
  have v_q18 := FIw_ScalarArithmetic.mul q q18 8#u32 h_q18
  have cv_q18 := v_q18.1
  have vv_q18 := v_q18.2
  have v_q19 := FIw_ScalarArithmetic.mul note_first q19 18#u32 h_q19
  have cv_q19 := v_q19.1
  have vv_q19 := v_q19.2
  have v_q20 := FIv_NativeValue.add q18 q19 q20 cv_q18 cv_q19 h_q20
  have cv_q20 := v_q20.1
  have vv_q20 := v_q20.2
  have v_q21 := FIw_ScalarArithmetic.mul q3 q21 16#u32 h_q21
  have cv_q21 := v_q21.1
  have vv_q21 := v_q21.2
  have v_length := FIv_NativeValue.add q20 q21 length cv_q20 cv_q21 h_length
  have cv_length := v_length.1
  have vv_length := v_length.2
  have cv_q22 := FIv_NativeArray.canonical initial poseidon2.RATE q22 cv_initial h_q22
  have vv_q22 := FIw_ArrayReadValue.read initial poseidon2.RATE (FIx_ScheduleIndices.rate_bound) q22 h_q22
  have v_q23 := FIv_NativeValue.mul q9 domain q23 cv_q9 cv_domain h_q23
  have cv_q23 := v_q23.1
  have vv_q23 := v_q23.2
  have v_q24 := FIv_SubMap.qm q22 q23 q24 cv_q22 cv_q23 h_q24
  have cv_q24 := v_q24.1
  have vv_q24 := v_q24.2
  have v_initial1 := FIw_ArrayValue.update initial initial1 poseidon2.RATE q24 (FIx_ScheduleIndices.rate_bound) cv_initial cv_q24 h_initial1
  have cv_initial1 := v_initial1.1
  have vv_initial1 := v_initial1.2
  have vi : i.val=9 := FIx_ScheduleIndices.rate_plus_one i h_i
  have cv_q25 := FIv_NativeArray.canonical initial1 i q25 cv_initial1 h_q25
  have vv_q25 := FIw_ArrayReadValue.read initial1 i (FIx_ScheduleIndices.nine_bound i vi) q25 h_q25
  have v_q26 := FIv_NativeValue.mul q9 length q26 cv_q9 cv_length h_q26
  have cv_q26 := v_q26.1
  have vv_q26 := v_q26.2
  have v_q27 := FIv_SubMap.qm q25 q26 q27 cv_q25 cv_q26 h_q27
  have cv_q27 := v_q27.1
  have vv_q27 := v_q27.2
  have v_initial2 := FIw_ArrayValue.update initial1 initial2 i q27 (FIx_ScheduleIndices.nine_bound i vi) cv_initial1 cv_q27 h_initial2
  have cv_initial2 := v_initial2.1
  have vv_initial2 := v_initial2.2
  have v_q28 := FIv_NativeValue.add q q1 q28 cv_q cv_q1 h_q28
  have cv_q28 := v_q28.1
  have vv_q28 := v_q28.2
  have cv_q29 := FIv_NativeArray.canonical selectors.high 2#usize q29 hh h_q29
  have vv_q29 : decode q29=high selectors (2#usize).val := (FIv_NativeArray.read selectors.high 2#usize q29 h_q29).symm
  have v_q30 := FIv_NativeValue.add q28 q29 q30 cv_q28 cv_q29 h_q30
  have cv_q30 := v_q30.1
  have vv_q30 := v_q30.2
  have v_q31 := FIv_NativeValue.add q30 q3 q31 cv_q30 cv_q3 h_q31
  have cv_q31 := v_q31.1
  have vv_q31 := v_q31.2
  have cv_q32 := FIv_NativeArray.canonical selectors.high 26#usize q32 hh h_q32
  have vv_q32 : decode q32=high selectors (26#usize).val := (FIv_NativeArray.read selectors.high 26#usize q32 h_q32).symm
  have v_q33 := FIv_NativeValue.add q31 q32 q33 cv_q31 cv_q32 h_q33
  have cv_q33 := v_q33.1
  have vv_q33 := v_q33.2
  have v_q34 := FIv_NativeValue.add q33 q5 q34 cv_q33 cv_q5 h_q34
  have cv_q34 := v_q34.1
  have vv_q34 := v_q34.2
  have cv_q35 := FIv_NativeArray.canonical selectors.high 31#usize q35 hh h_q35
  have vv_q35 : decode q35=high selectors (31#usize).val := (FIv_NativeArray.read selectors.high 31#usize q35 h_q35).symm
  have v_chunk_eight := FIv_NativeValue.add q34 q35 chunk_eight cv_q34 cv_q35 h_chunk_eight
  have cv_chunk_eight := v_chunk_eight.1
  have vv_chunk_eight := v_chunk_eight.2
  have cv_q36 := FIv_NativeArray.canonical selectors.high 3#usize q36 hh h_q36
  have vv_q36 : decode q36=high selectors (3#usize).val := (FIv_NativeArray.read selectors.high 3#usize q36 h_q36).symm
  have cv_q37 := FIv_NativeArray.canonical selectors.high 32#usize q37 hh h_q37
  have vv_q37 : decode q37=high selectors (32#usize).val := (FIv_NativeArray.read selectors.high 32#usize q37 h_q37).symm
  have v_chunk_two := FIv_NativeValue.add q36 q37 chunk_two cv_q36 cv_q37 h_chunk_two
  have cv_chunk_two := v_chunk_two.1
  have vv_chunk_two := v_chunk_two.2
  have v_chunk_eight1 := FIv_NativeValue.add chunk_eight private_chunk_eight chunk_eight1 cv_chunk_eight cv_private_chunk_eight h_chunk_eight1
  have cv_chunk_eight1 := v_chunk_eight1.1
  have vv_chunk_eight1 := v_chunk_eight1.2
  have v_chunk_two1 := FIv_NativeValue.add chunk_two private_chunk_two chunk_two1 cv_chunk_two cv_private_chunk_two h_chunk_two1
  have cv_chunk_two1 := v_chunk_two1.1
  have vv_chunk_two1 := v_chunk_two1.2
  have cv_q38 := FIv_NativeArray.canonical selectors.low 12#usize q38 hl h_q38
  have vv_q38 : decode q38=low selectors (12#usize).val := (FIv_NativeArray.read selectors.low 12#usize q38 h_q38).symm
  have v_absorption := FIx_AbsorptionArray.value q38 fixed chunk_two1 chunk_eight1 nodes openings.z absorption
    cv_q38 cv_fixed cv_chunk_two1 cv_chunk_eight1 cv_nodes hz h_absorption
  have vv_absorption := FIx_ArrayMeaning.decoded_of_map absorption _ v_absorption.2
  have math_full_initial_selector : decode full_initial_selector=FIx_ScheduleModel.full public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_q12 : decode q12=FIx_ScheduleModel.fullRate public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_domain : decode domain=FIx_ScheduleModel.domain public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_length : decode length=FIx_ScheduleModel.length public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_chunk_eight1 : decode chunk_eight1=FIx_ScheduleModel.chunkEight public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_chunk_two1 : decode chunk_two1=FIx_ScheduleModel.chunkTwo public1.variant selectors := by
    simp only [vv_q38,vv_chunk_two1,vv_chunk_eight1,vv_chunk_two,vv_q37,vv_q36,vv_chunk_eight,vv_q35,vv_q34,vv_q33,vv_q32,vv_q31,vv_q30,vv_q29,vv_q28,vv_length,vv_q21,vv_q20,vv_q19,vv_q18,vv_domain,vv_q17,vv_q16,vv_q15,vv_q14,vv_note_first,vv_q13,vv_q12,vv_rate_initial_selector,vv_full_initial_selector,vv_q11,vv_q10,vv_q9,vv_private_chunk_two,vv_private_chunk_eight,vv_fixed,vv_transfer_first,vv_q8,vv_q7,vv_q6,vv_first_common,vv_q5,vv_q4,vv_q3,vv_q2,vv_q1,vv_q,vv_nodes]
    simp only [FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.chunkEight,FIx_ScheduleModel.chunkTwo,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]
    rfl
  have math_fixed : decode fixed=(FIx_ScheduleModel.variant public1.variant selectors).2.1 := by
    rw [vv_fixed,vv_q6,vv_q7,vv_q8]
    rfl
  have math_raw : decoded initial=FIx_ScheduleModel.initialRaw public1.variant selectors openings := by
    rw [vv_initial,math_q12,math_full_initial_selector]
    rfl
  refine ⟨cv_initial2,v_absorption.1,?_,?_⟩
  · rw [vv_initial2,vv_q27,vv_q26,vv_q25,vv_initial1,vv_q24,vv_q23,vv_q22,
      FIx_InitialWrites.nine_fin i vi,FIx_InitialWrites.rate_fin,math_raw,math_domain,math_length,vv_q9]
    exact FIx_InitialWrites.value (FIx_ScheduleModel.initialRaw public1.variant selectors openings)
      (low selectors 0) (FIx_ScheduleModel.domain public1.variant selectors)
      (FIx_ScheduleModel.length public1.variant selectors)
  · rw [vv_absorption,math_chunk_two1,math_chunk_eight1,math_fixed,vv_nodes,vv_q38]
    rfl
#print axioms value
end AspisR1.FIx_ScheduleValue
end
