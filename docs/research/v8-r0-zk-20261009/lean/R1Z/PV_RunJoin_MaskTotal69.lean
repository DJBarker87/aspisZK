import R1Z.PV_RunJoin_MaskRangeTotal69
import R1Z.PV_RunJoin_MaskLinearsTotal69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_B3_Range117 PV_RunJoin_MaskFieldTotal69

abbrev Q := aspis_core.field.QM31

theorem selected_values (i : Usize) (hi : i∈selectedIndices) :
    ∃ e,Array.index_usize host_arithmetic.FACTOR_EXPONENTS i=ok e ∧ e.val<27 := by
  simp only [selectedIndices,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨0#u8,PV_B3_ZeroMask117.factor0,by decide⟩
  · exact ⟨2#u8,PV_B3_ZeroMask117.factor1,by decide⟩
  · exact ⟨4#u8,PV_B3_ZeroMask117.factor2,by decide⟩
  · exact ⟨6#u8,PV_B3_ZeroMask117.factor3,by decide⟩
  · exact ⟨8#u8,PV_B3_ZeroMask117.factor4,by decide⟩
  · exact ⟨10#u8,PV_B3_ZeroMask117.factor5,by decide⟩
  · exact ⟨12#u8,PV_B3_ZeroMask117.factor6,by decide⟩
  · exact ⟨14#u8,PV_B3_ZeroMask117.factor7,by decide⟩
  · exact ⟨16#u8,PV_B3_ZeroMask117.factor8,by decide⟩
  · exact ⟨18#u8,PV_B3_ZeroMask117.factor9,by decide⟩
  · exact ⟨20#u8,PV_B3_ZeroMask117.factor10,by decide⟩
  · exact ⟨22#u8,PV_B3_ZeroMask117.factor11,by decide⟩
  · exact ⟨24#u8,PV_B3_ZeroMask117.factor12,by decide⟩
  · exact ⟨26#u8,PV_B3_ZeroMask117.factor13,by decide⟩
  · exact ⟨13#u8,PV_B3_ZeroMask117.factor14,by decide⟩
  · exact ⟨25#u8,PV_B3_ZeroMask117.factor15,by decide⟩

theorem mask_values (i : Usize) (hi : i∈maskIndices) :
    ∃ e,Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS i=ok e ∧ e.val<27 := by
  simp only [maskIndices,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨1#u8,PV_B3_ZeroMask117.maskfactor0,by decide⟩
  · exact ⟨3#u8,PV_B3_ZeroMask117.maskfactor1,by decide⟩
  · exact ⟨5#u8,PV_B3_ZeroMask117.maskfactor2,by decide⟩
  · exact ⟨7#u8,PV_B3_ZeroMask117.maskfactor3,by decide⟩
  · exact ⟨9#u8,PV_B3_ZeroMask117.maskfactor4,by decide⟩
  · exact ⟨11#u8,PV_B3_ZeroMask117.maskfactor5,by decide⟩
  · exact ⟨15#u8,PV_B3_ZeroMask117.maskfactor6,by decide⟩
  · exact ⟨17#u8,PV_B3_ZeroMask117.maskfactor7,by decide⟩
  · exact ⟨19#u8,PV_B3_ZeroMask117.maskfactor8,by decide⟩
  · exact ⟨21#u8,PV_B3_ZeroMask117.maskfactor9,by decide⟩

theorem complete (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) :
    ∃ out,host_arithmetic.state_only_selected_mask_value c1 mask g point=ok out := by
  obtain ⟨⟨linear,explicit_linear⟩,hl⟩ := PV_RunJoin_MaskLinearsTotal69.complete point
  have selected_bound : ∀ i∈selectedIndices,i.val<(16#usize).val := by
    intro i hi
    have h : i.val∈selectedIndices.map (fun j => j.val) := List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [selected_order] at h
    exact List.mem_range.mp h
  have mask_bound : ∀ i∈maskIndices,i.val<(10#usize).val := by
    intro i hi
    have h : i.val∈maskIndices.map (fun j => j.val) := List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [mask_order] at h
    exact List.mem_range.mp h
  have horner_bound : ∀ i∈hornerIndices,i.val<27 := by
    intro i hi
    have h : i.val∈hornerIndices.map (fun j => j.val) := List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [horner_order,List.mem_reverse] at h
    have small := List.mem_range.mp h
    omega
  obtain ⟨coefficients,hc⟩ := PV_RunJoin_MaskRangeTotal69.scatter c1 host_arithmetic.FACTOR_EXPONENTS
    selectedIndices (Array.repeat 27#usize aspis_core.field.QM31.ZERO) selected_bound selected_values
  obtain ⟨coefficients1,hc1⟩ := PV_RunJoin_MaskRangeTotal69.scatter mask host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
    maskIndices coefficients mask_bound mask_values
  obtain ⟨prepared,hp⟩ := PV_RunJoin_MaskPreparedTotal69.prepare linear
  obtain ⟨shared,hs⟩ := ProverRwP6ArrayRead.read coefficients1
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE (by unfold aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE;decide)
  obtain ⟨shared1,hs1⟩ := PV_RunJoin_MaskRangeTotal69.horner coefficients1 prepared hornerIndices shared horner_bound
  obtain ⟨power,hpow⟩ := PV_RunJoin_MaskPreparedTotal69.power explicit_linear
  obtain ⟨factor,hf⟩ := qadd aspis_core.field.QM31.ONE power
  obtain ⟨explicit_value,he⟩ := qmul factor g
  obtain ⟨out,ho⟩ := qadd shared1 explicit_value
  refine ⟨out,?_⟩
  rw [PV_B3_AuditSourceD324.Mask117.source]
  simp only [PV_B3_AuditSourceD324.Mask117.reference,hl,bind_tc_ok,Aeneas.Std.uncurry]
  dsimp only
  simp only [hc,hc1,hp,hs,hs1,hpow,hf,he,ho,bind_tc_ok]

#print axioms selected_values
#print axioms mask_values
#print axioms complete
end R1Z.PV_RunJoin_MaskTotal69
