import S9ActualPairOldPrimitiveSuccessV1
import S9PairCallerBodyPrefixV1
import S9CandidateUpdateResultMapV1
import S9ActualPairHelperBodyPrefixV1
import S9ActualPairWideOutputCanonicalV1
import S9ActualPairScalarCallbackV1
import S9PairArrayUpdateCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairAfterLowMapV1
open AspisR1S9ActualPairHelperBodyPrefixV1
open AspisR1S9ActualPairOldCarrierScalarV1
open AspisR1S9ActualPairOldPrimitiveSuccessV1
abbrev Q := aspis_core.field.QM31
abbrev W := AspisR1S9ActualPairHelperBodyPrefixV1.W
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev QC := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩
private theorem index_map {A B : Type} {n : Usize} (f : A → B)
    (a : Array A n) (i : Usize) (v : A) (h : Array.index_usize a i = .ok v) :
    Array.index_usize (mapArray f a) i = .ok (f v) := by
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a i
  rw [h] at hm
  exact hm.symm
private theorem make_map {A B : Type} (f : A → B) (a b c d : A) :
    mapArray f (Array.make 4#usize [a,b,c,d]) = Array.make 4#usize [f a,f b,f c,f d] := by
  rfl
private theorem update_map (a out : W) (i : Usize) (v : Wide)
    (hi : i.val < 4) (h : Array.update a i v = .ok out) :
    Array.update (mapArray toOldW a) i (toOldW v) = .ok (mapArray toOldW out) := by
  have hm := AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result toOldW a i v hi
  rw [h] at hm
  exact hm.symm

/-- Every successful actual post-scalar continuation preserves canonical
weight reads. Inputs q41/q8/q12/q16 may be arbitrary: actual mixed
multiplication canonicalises them before use. -/
theorem actual_after_low_success_maps (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : Wide) (flow : ControlFlow (R × W) W)
    (hcq41 : QC q41) (hcq16 : QC q16)
    (hap : GoodArray ap1) (hw : GoodArray weights) (hl : WC low)
    (h : pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow) :
    ∃ output, flow = .cont (iterNext,output) ∧
      AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
        (mapArray toOldW ap1) side iterNext (mapArray toOldW weights)
        (toOldQ q41) (toOldQ q8) (toOldQ q12) (toOldQ q16) (toOldW low) =
        .ok (.cont (iterNext,mapArray toOldW output)) := by
  unfold pairAfterLow at h
  obtain ⟨i,hi,hstep1⟩ := bind_success _ _ _ h
  obtain ⟨we,hwe,hstep2⟩ := bind_success _ _ _ hstep1
  obtain ⟨q5,hq5,hstep3⟩ := bind_success _ _ _ hstep2
  obtain ⟨we1,hwe1,hstep4⟩ := bind_success _ _ _ hstep3
  obtain ⟨term0,hterm0,hstep5⟩ := bind_success _ _ _ hstep4
  obtain ⟨i1,hi1,hstep6⟩ := bind_success _ _ _ hstep5
  obtain ⟨we2,hwe2,hstep7⟩ := bind_success _ _ _ hstep6
  obtain ⟨q6,hq6,hstep8⟩ := bind_success _ _ _ hstep7
  obtain ⟨we3,hwe3,hstep9⟩ := bind_success _ _ _ hstep8
  obtain ⟨term1,hterm1,hstep10⟩ := bind_success _ _ _ hstep9
  obtain ⟨i2,hi2,hstep11⟩ := bind_success _ _ _ hstep10
  obtain ⟨we4,hwe4,hstep12⟩ := bind_success _ _ _ hstep11
  obtain ⟨q7,hq7,hstep13⟩ := bind_success _ _ _ hstep12
  obtain ⟨we5,hwe5,hstep14⟩ := bind_success _ _ _ hstep13
  obtain ⟨term2,hterm2,hstep15⟩ := bind_success _ _ _ hstep14
  obtain ⟨i3,hi3,hstep16⟩ := bind_success _ _ _ hstep15
  obtain ⟨we6,hwe6,hstep17⟩ := bind_success _ _ _ hstep16
  obtain ⟨q9,hq9,hstep18⟩ := bind_success _ _ _ hstep17
  obtain ⟨we7,hwe7,hstep19⟩ := bind_success _ _ _ hstep18
  obtain ⟨term3,hterm3,hstep20⟩ := bind_success _ _ _ hstep19
  obtain ⟨we8,hwe8,hstep21⟩ := bind_success _ _ _ hstep20
  obtain ⟨we9,hwe9,hstep22⟩ := bind_success _ _ _ hstep21
  obtain ⟨first2,hfirst2,hstep23⟩ := bind_success _ _ _ hstep22
  obtain ⟨we10,hwe10,hstep24⟩ := bind_success _ _ _ hstep23
  obtain ⟨first3,hfirst3,hstep25⟩ := bind_success _ _ _ hstep24
  obtain ⟨we11,hwe11,hstep26⟩ := bind_success _ _ _ hstep25
  obtain ⟨all,hall,hstep27⟩ := bind_success _ _ _ hstep26
  have hcwe := hap i we hwe
  have hcwe2 := hap i1 we2 hwe2
  have hcwe4 := hap i2 we4 hwe4
  have hcwe6 := hap i3 we6 hwe6
  have hcwe1 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical we we1 q5 hcwe hwe1
  have hcterm0 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical we1 term0 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hcwe1 hterm0
  have hcwe3 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical we2 we3 q6 hcwe2 hwe3
  have hcterm1 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical we3 term1 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hcwe3 hterm1
  have hcwe5 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical we4 we5 q7 hcwe4 hwe5
  have hcterm2 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical we5 term2 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hcwe5 hterm2
  have hcwe7 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical we6 we7 q9 hcwe6 hwe7
  have hcterm3 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical we7 term3 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hcwe7 hterm3
  have hfixed0 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 0#usize = .ok term0 := by rfl
  have he0 : we8 = term0 := Result.ok.inj (hwe8.symm.trans hfixed0)
  subst we8
  have hfixed1 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 1#usize = .ok term1 := by rfl
  have he1 : we9 = term1 := Result.ok.inj (hwe9.symm.trans hfixed1)
  subst we9
  have hfixed2 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 2#usize = .ok term2 := by rfl
  have he2 : we10 = term2 := Result.ok.inj (hwe10.symm.trans hfixed2)
  subst we10
  have hfixed3 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 3#usize = .ok term3 := by rfl
  have he3 : we11 = term3 := Result.ok.inj (hwe11.symm.trans hfixed3)
  subst we11
  have hcfirst2 := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcterm0 hcterm1 hfirst2
  have hcfirst3 := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcfirst2 hcterm2 hfirst3
  have hcall := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcfirst3 hcterm3 hall
  have hperm : _root_.AspisR1S9ProductionPairCutV1.weights.PERM = AspisR1S9PairCallerStepV1.weights.PERM := by
    unfold _root_.AspisR1S9ProductionPairCutV1.weights.PERM AspisR1S9PairCallerStepV1.weights.PERM
    rfl
  have hquarter : _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER = AspisR1S9PairCallerStepV1.weights.QUARTER := by
    unfold _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER AspisR1S9PairCallerStepV1.weights.QUARTER
    rfl
  have mti : Array.index_usize AspisR1S9PairCallerStepV1.weights.PERM 0#usize = .ok i := by rw [←hperm]; exact hi
  have mtwe := index_map toOldW ap1 i we hwe
  have mtq5 := index_map toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) 0#usize q5 hq5
  simp only [make_map,one_maps] at mtq5
  have mtwe1 := wide_mul_qm31_success we we1 q5 hcwe hwe1
  have mtterm0 := wide_mul_m31_success we1 term0 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hterm0
  rw [hquarter] at mtterm0
  have mti1 : Array.index_usize AspisR1S9PairCallerStepV1.weights.PERM 1#usize = .ok i1 := by rw [←hperm]; exact hi1
  have mtwe2 := index_map toOldW ap1 i1 we2 hwe2
  have mtq6 := index_map toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) 1#usize q6 hq6
  simp only [make_map,one_maps] at mtq6
  have mtwe3 := wide_mul_qm31_success we2 we3 q6 hcwe2 hwe3
  have mtterm1 := wide_mul_m31_success we3 term1 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hterm1
  rw [hquarter] at mtterm1
  have mti2 : Array.index_usize AspisR1S9PairCallerStepV1.weights.PERM 2#usize = .ok i2 := by rw [←hperm]; exact hi2
  have mtwe4 := index_map toOldW ap1 i2 we4 hwe4
  have mtq7 := index_map toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) 2#usize q7 hq7
  simp only [make_map,one_maps] at mtq7
  have mtwe5 := wide_mul_qm31_success we4 we5 q7 hcwe4 hwe5
  have mtterm2 := wide_mul_m31_success we5 term2 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hterm2
  rw [hquarter] at mtterm2
  have mti3 : Array.index_usize AspisR1S9PairCallerStepV1.weights.PERM 3#usize = .ok i3 := by rw [←hperm]; exact hi3
  have mtwe6 := index_map toOldW ap1 i3 we6 hwe6
  have mtq9 := index_map toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) 3#usize q9 hq9
  simp only [make_map,one_maps] at mtq9
  have mtwe7 := wide_mul_qm31_success we6 we7 q9 hcwe6 hwe7
  have mtterm3 := wide_mul_m31_success we7 term3 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hterm3
  rw [hquarter] at mtterm3
  have mtread0 : Array.index_usize (Array.make 4#usize [toOldW term0,toOldW term1,toOldW term2,toOldW term3]) 0#usize = .ok (toOldW term0) := by rfl
  have mtread1 : Array.index_usize (Array.make 4#usize [toOldW term0,toOldW term1,toOldW term2,toOldW term3]) 1#usize = .ok (toOldW term1) := by rfl
  have mtread2 : Array.index_usize (Array.make 4#usize [toOldW term0,toOldW term1,toOldW term2,toOldW term3]) 2#usize = .ok (toOldW term2) := by rfl
  have mtread3 : Array.index_usize (Array.make 4#usize [toOldW term0,toOldW term1,toOldW term2,toOldW term3]) 3#usize = .ok (toOldW term3) := by rfl
  have mtfirst2 := wide_add_success term0 term1 first2 hcterm0 hcterm1 hfirst2
  have mtfirst3 := wide_add_success first2 term2 first3 hcfirst2 hcterm2 hfirst3
  have mtall := wide_add_success first3 term3 all hcfirst3 hcterm3 hall
  split at hstep27
  · rename_i hside
    obtain ⟨we12,hwe12,hstep28⟩ := bind_success _ _ _ hstep27
    obtain ⟨weights1,hweights1,hstep29⟩ := bind_success _ _ _ hstep28
    obtain ⟨we13,hwe13,hstep30⟩ := bind_success _ _ _ hstep29
    obtain ⟨we14,hwe14,hstep31⟩ := bind_success _ _ _ hstep30
    obtain ⟨a,ha,hstep32⟩ := bind_success _ _ _ hstep31
    have hc12 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcall hwe12
    have hc13 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcfirst3 hwe13
    have hc14 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc13 hwe14
    have mtwe12 := wide_mul_success low all we12 hl hcall hwe12
    have mtweights1 := update_map weights weights1 0#usize we12 (by decide) hweights1
    have mtwe13 := wide_mul_success low first3 we13 hl hcfirst3 hwe13
    have mtwe14 := wide_mul_qm31_success we13 we14 q16 hc13 hwe14
    have mta := update_map weights1 a 1#usize we14 (by decide) ha
    refine ⟨a,(Result.ok.inj hstep32).symm,?_⟩
    unfold AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
    simp only [mti,mtwe,mtq5,mtwe1,mtterm0,mti1,mtwe2,mtq6,mtwe3,mtterm1,mti2,mtwe4,mtq7,mtwe5,mtterm2,mti3,mtwe6,mtq9,mtwe7,mtterm3,mtread0,mtread1,mtread2,mtread3,mtfirst2,mtfirst3,mtall,hside,↓reduceIte,mtwe12,mtweights1,mtwe13,mtwe14,mta,bind_tc_ok]

  · rename_i hside
    obtain ⟨we12,hwe12,hstep33⟩ := bind_success _ _ _ hstep27
    obtain ⟨we13,hwe13,hstep34⟩ := bind_success _ _ _ hstep33
    obtain ⟨we14,hwe14,hstep35⟩ := bind_success _ _ _ hstep34
    obtain ⟨we15,hwe15,hstep36⟩ := bind_success _ _ _ hstep35
    obtain ⟨we16,hwe16,hstep37⟩ := bind_success _ _ _ hstep36
    obtain ⟨weights1,hweights1,hstep38⟩ := bind_success _ _ _ hstep37
    obtain ⟨we17,hwe17,hstep39⟩ := bind_success _ _ _ hstep38
    obtain ⟨we18,hwe18,hstep40⟩ := bind_success _ _ _ hstep39
    obtain ⟨weights2,hweights2,hstep41⟩ := bind_success _ _ _ hstep40
    obtain ⟨we19,hwe19,hstep42⟩ := bind_success _ _ _ hstep41
    obtain ⟨q10,hq10,hstep43⟩ := bind_success _ _ _ hstep42
    obtain ⟨we20,hwe20,hstep44⟩ := bind_success _ _ _ hstep43
    obtain ⟨a,ha,hstep45⟩ := bind_success _ _ _ hstep44
    have hc12 := hw 1#usize we12 hwe12
    have hc13 := hap i3 we13 hwe13
    have hc14 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical _ _ _ hc13 hwe14
    have hc15 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hc14 hwe15
    have hc16 := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hc12 hc15 hwe16
    have hc17 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcall hwe17
    have hc18 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc17 hwe18
    have hc19 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcfirst2 hwe19
    have hc20 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc19 hwe20
    have mtwe12 := index_map toOldW weights 1#usize we12 hwe12
    have mtwe13 := index_map toOldW ap1 i3 we13 hwe13
    have mtwe14 := wide_mul_m31_success we13 we14 _root_.AspisR1S9ProductionPairCutV1.weights.QUARTER hwe14
    rw [hquarter] at mtwe14
    have he13 : we13 = we6 := Result.ok.inj (hwe13.symm.trans hwe6)
    rw [he13] at mtwe14
    have mtwe15 := wide_mul_success low we14 we15 hl hc14 hwe15
    have mtwe16 := wide_add_success we12 we15 we16 hc12 hc15 hwe16
    have mtweights1 := update_map weights weights1 1#usize we16 (by decide) hweights1
    have mtwe17 := wide_mul_success low all we17 hl hcall hwe17
    have mtwe18 := wide_mul_qm31_success we17 we18 q41 hc17 hwe18
    have mtweights2 := update_map weights1 weights2 2#usize we18 (by decide) hweights2
    have mtwe19 := wide_mul_success low first2 we19 hl hcfirst2 hwe19
    have mtq10 := qm_mul_success q16 q41 q10 hcq16 hcq41 hq10
    have mtwe20 := wide_mul_qm31_success we19 we20 q10 hc19 hwe20
    have mta := update_map weights2 a 3#usize we20 (by decide) ha
    refine ⟨a,(Result.ok.inj hstep45).symm,?_⟩
    unfold AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
    simp only [mti,mtwe,mtq5,mtwe1,mtterm0,mti1,mtwe2,mtq6,mtwe3,mtterm1,mti2,mtwe4,mtq7,mtwe5,mtterm2,mti3,mtwe6,mtq9,mtwe7,mtterm3,mtread0,mtread1,mtread2,mtread3,mtfirst2,mtfirst3,mtall,hside,↓reduceIte,mtwe12,mtwe13,mtwe14,mtwe15,mtwe16,mtweights1,mtwe17,mtwe18,mtweights2,mtwe19,mtq10,mtwe20,mta,bind_tc_ok]

#print axioms actual_after_low_success_maps
end AspisR1S9ActualPairAfterLowMapV1
