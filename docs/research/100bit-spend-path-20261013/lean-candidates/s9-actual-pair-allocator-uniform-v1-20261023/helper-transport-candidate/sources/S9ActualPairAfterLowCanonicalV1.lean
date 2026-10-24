import S9ActualPairHelperBodyPrefixV1
import S9ActualPairWideOutputCanonicalV1
import S9ActualPairScalarCallbackV1
import S9PairArrayUpdateCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairAfterLowCanonicalV1
open AspisR1S9ActualPairHelperBodyPrefixV1
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩
private theorem map_id (a : W) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapArray (fun (x : Wide) => x) a = a := by
  cases a
  simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapArray]
private theorem update_good (a out : W) (i : Usize) (v : Wide)
    (hi : i.val < 4) (ha : GoodArray a) (hv : WC v)
    (h : Array.update a i v = .ok out) : GoodArray out := by
  have hinput : ∀ (j : Usize) (v : Wide),
      Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray (fun (x : Wide) => x) a) j = .ok v → WC v := by
    intro j v hr
    rw [map_id a] at hr
    exact ha j v hr
  have hc := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    (fun (x : Wide) => x) WC a i v out hi h hinput hv
  intro j x hr
  apply hc j x
  change Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray (fun (y : Wide) => y) out) j = .ok x
  rw [map_id out]
  exact hr

/-- Every successful actual post-scalar continuation preserves canonical
weight reads. Inputs q41/q8/q12/q16 may be arbitrary: actual mixed
multiplication canonicalises them before use. -/
theorem actual_after_low_preserves (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : Wide) (flow : ControlFlow (R × W) W)
    (hap : GoodArray ap1) (hw : GoodArray weights) (hl : WC low)
    (h : pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow) :
    ∃ output, flow = .cont (iterNext,output) ∧ GoodArray output := by
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
  have hi0 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 0#usize = .ok term0 := by rfl
  have he0 : we8 = term0 := Result.ok.inj (hwe8.symm.trans hi0)
  subst we8
  have hi1 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 1#usize = .ok term1 := by rfl
  have he1 : we9 = term1 := Result.ok.inj (hwe9.symm.trans hi1)
  subst we9
  have hi2 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 2#usize = .ok term2 := by rfl
  have he2 : we10 = term2 := Result.ok.inj (hwe10.symm.trans hi2)
  subst we10
  have hi3 : Array.index_usize (Array.make 4#usize [term0,term1,term2,term3]) 3#usize = .ok term3 := by rfl
  have he3 : we11 = term3 := Result.ok.inj (hwe11.symm.trans hi3)
  subst we11
  have hcfirst2 := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcterm0 hcterm1 hfirst2
  have hcfirst3 := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcfirst2 hcterm2 hfirst3
  have hcall := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical _ _ _ hcfirst3 hcterm3 hall
  split at hstep27
  · obtain ⟨we12,hwe12,hstep28⟩ := bind_success _ _ _ hstep27
    obtain ⟨weights1,hweights1,hstep29⟩ := bind_success _ _ _ hstep28
    obtain ⟨we13,hwe13,hstep30⟩ := bind_success _ _ _ hstep29
    obtain ⟨we14,hwe14,hstep31⟩ := bind_success _ _ _ hstep30
    obtain ⟨a,ha,hstep32⟩ := bind_success _ _ _ hstep31
    have hc12 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcall hwe12
    have hw1 := update_good weights weights1 0#usize we12 (by decide) hw hc12 hweights1
    have hc13 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcfirst3 hwe13
    have hc14 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc13 hwe14
    have hwa := update_good weights1 a 1#usize we14 (by decide) hw1 hc14 ha
    exact ⟨a,(Result.ok.inj hstep32).symm,hwa⟩
  · obtain ⟨we12,hwe12,hstep33⟩ := bind_success _ _ _ hstep27
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
    have hw1 := update_good weights weights1 1#usize we16 (by decide) hw hc16 hweights1
    have hc17 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcall hwe17
    have hc18 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc17 hwe18
    have hw2 := update_good weights1 weights2 2#usize we18 (by decide) hw1 hc18 hweights2
    have hc19 := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_success_canonical _ _ _ hl hcfirst2 hwe19
    have hc20 := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical _ _ _ hc19 hwe20
    have hwa := update_good weights2 a 3#usize we20 (by decide) hw2 hc20 ha
    exact ⟨a,(Result.ok.inj hstep45).symm,hwa⟩
#print axioms actual_after_low_preserves
end AspisR1S9ActualPairAfterLowCanonicalV1
