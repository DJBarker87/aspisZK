import ExtractedMaskCoefficientWriteMeaning
import ExtractedMaskCoefficientLoop0
import ExtractedMaskCoefficientLoop1

/-! Draft only: pointwise invariants for the two symbolic coefficient-write
folds. The induction follows the actual forward iterator but does not unroll
its 16 or 10 iterations. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCoefficientLoopMeaning

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientArray
open AspisR1.ExtractedMaskCoefficientSchedule

abbrev QM := field.QM31
abbrev C1 := AspisR1.ExtractedMaskCoefficientStep.C1
abbrev MaskOnly := AspisR1.ExtractedMaskCoefficientStep.MaskOnly
abbrev Coefficients := AspisR1.ExtractedMaskCoefficientStep.Coefficients
abbrev Range := core.ops.range.Range Usize
abbrev CanonicalQM := AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
abbrev CanonicalArray := AspisR1.ExtractedMaskCoefficientStep.CanonicalArray
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def c1Meaning (c1 : C1) (j : Fin 16) : ExactQM :=
  AspisR1.ExtractedMaskTowerBasisExact.basisElement (j.val % 4) *
    AspisR1.ExtractedMaskQM31Exact.decode
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j)

def maskMeaning (maskOnly : MaskOnly) (j : Fin 10) : ExactQM :=
  AspisR1.ExtractedMaskTowerBasisExact.basisElement (j.val % 4) *
    AspisR1.ExtractedMaskQM31Exact.decode
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j)

/-- Interval invariant for the first source schedule. Every destination whose
column has already been consumed contains its exact transformed source value;
all coefficients outside the consumed schedule remain at their initial value. -/
theorem loop0_model_interval
    (c1 : C1) (initial : Coefficients) (iter : Range) (fuel : Nat)
    (hend : iter.end.val = 16) (hspan : iter.start.val + fuel = 16)
    (hsource : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j)) :
    (∀ j : Fin 16, iter.start.val ≤ j.val → j.val < 16 →
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop0.writeModel0 c1 initial iter fuel)
          (c1Exponent j) = c1Meaning c1 j) ∧
    (∀ e : Fin 27,
      (∀ j : Fin 16, iter.start.val ≤ j.val → j.val < 16 → c1Exponent j ≠ e) →
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop0.writeModel0 c1 initial iter fuel) e =
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients initial e) := by
  induction fuel generalizing iter initial with
  | zero =>
      have hstart : iter.start.val = 16 := by omega
      constructor
      · intro j hlow hhigh
        omega
      · intro e houtside
        simp [AspisR1.ExtractedMaskCoefficientLoop0.writeModel0]
  | succ fuel ih =>
      have hstartlt : iter.start.val < iter.end.val := by omega
      obtain ⟨iter1, hnext, hinc, hend1, _⟩ :=
        AspisR1.ExtractedMaskForwardRange.next_step iter hstartlt
      have hcolumn : iter.start.val < 16 := by omega
      have hend1' : iter1.end.val = 16 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 16 := by omega
      have hstart1 : iter1.start.val = iter.start.val + 1 := hinc
      have hnext' :
          core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
            .ok (some iter.start, iter1) := hnext
      have hwrite :=
        AspisR1.ExtractedMaskCoefficientWriteMeaning.decoded_writeAt0
          c1 initial iter.start hcolumn (by simpa using hsource ⟨iter.start.val, hcolumn⟩)
      let after := AspisR1.ExtractedMaskCoefficientLoop0.writeAt0
        c1 initial iter.start hcolumn
      have hmodel :
          AspisR1.ExtractedMaskCoefficientLoop0.writeModel0 c1 initial iter (fuel + 1) =
            AspisR1.ExtractedMaskCoefficientLoop0.writeModel0 c1 after iter1 fuel := by
        simp [AspisR1.ExtractedMaskCoefficientLoop0.writeModel0,
          hnext', hcolumn, after]
      have hih := ih after iter1 hend1' hspan1
      constructor
      · intro j hlow hhigh
        rw [hmodel]
        by_cases hj : j.val = iter.start.val
        · have hji : j = ⟨iter.start.val, hcolumn⟩ := Fin.ext hj
          have hnoFuture : ∀ k : Fin 16,
              iter1.start.val ≤ k.val → k.val < 16 → c1Exponent k ≠ c1Exponent j := by
            intro k hklo hkhigh heq
            have hkj : k.val = j.val := congrArg Fin.val (factor_schedule_injective heq)
            have hjv : j.val = iter.start.val := by simp [hji]
            omega
          have hkeep := hih.2 (c1Exponent j) hnoFuture
          rw [hji, hwrite, Function.update_self] at hkeep
          simpa [c1Meaning, hji] using hkeep
        · have hjlo : iter1.start.val ≤ j.val := by omega
          exact hih.1 j hjlo hhigh
      · intro e houtside
        rw [hmodel]
        have hfirst : c1Exponent ⟨iter.start.val, hcolumn⟩ ≠ e := by
          exact houtside ⟨iter.start.val, hcolumn⟩ (Nat.le_refl _) hcolumn
        have hnoFuture : ∀ j : Fin 16,
            iter1.start.val ≤ j.val → j.val < 16 → c1Exponent j ≠ e := by
          intro j hjlo hjhi
          exact houtside j (by omega) hjhi
        have hkeep := hih.2 e hnoFuture
        rw [hwrite, Function.update_of_ne hfirst.symm] at hkeep
        exact hkeep

/-- Full-range actual loop-0 output inherits the pointwise schedule meaning.
The initial array needs canonical cells only for the extracted loop's checked
body operations; the pointwise model theorem itself has no such premise. -/
theorem loop0_full_range
    (c1 : C1) (initial : Coefficients)
    (hsource : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hinitial : CanonicalArray initial) :
    ∃ out : Coefficients,
      state_only_hiding.state_only_selected_mask_value_loop0
        { start := 0#usize, «end» := 16#usize } c1 initial = .ok out ∧
      CanonicalArray out ∧
      (∀ j : Fin 16,
        AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients out
          (c1Exponent j) = c1Meaning c1 j) ∧
      (∀ e : Fin 27,
        (∀ j : Fin 16, c1Exponent j ≠ e) →
        AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients out e =
          AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients initial e) := by
  let iter : Range := { start := 0#usize, «end» := 16#usize }
  obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
    AspisR1.ExtractedMaskCoefficientLoop0.loop0_exec c1 iter initial 16 rfl (by rfl)
      hsource hinitial
  have hmeaning := loop0_model_interval c1 initial iter 16 rfl (by rfl) hsource
  refine ⟨out, ?_, hcanonical, ?_, ?_⟩
  · simpa [iter] using hrun
  · intro j
    have hj := hmeaning.1 j (Nat.zero_le _) j.isLt
    rw [hmodel]
    simpa [iter] using hj
  · intro e houtside
    have h := hmeaning.2 e (by
      intro j _ _
      exact houtside j)
    rw [hmodel]
    simpa [iter] using h

/-- Interval invariant for the second source schedule. Earlier C1 writes are
represented by the supplied initial array and are preserved at every cell not
in the consumed mask-only schedule. -/
theorem loop1_model_interval
    (maskOnly : MaskOnly) (initial : Coefficients) (iter : Range) (fuel : Nat)
    (hend : iter.end.val = 10) (hspan : iter.start.val + fuel = 10)
    (hsource : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j)) :
    (∀ j : Fin 10, iter.start.val ≤ j.val → j.val < 10 →
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop1.writeModel1 maskOnly initial iter fuel)
          (maskExponent j) = maskMeaning maskOnly j) ∧
    (∀ e : Fin 27,
      (∀ j : Fin 10, iter.start.val ≤ j.val → j.val < 10 → maskExponent j ≠ e) →
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop1.writeModel1 maskOnly initial iter fuel) e =
      AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients initial e) := by
  induction fuel generalizing iter initial with
  | zero =>
      have hstart : iter.start.val = 10 := by omega
      constructor
      · intro j hlow hhigh
        omega
      · intro e houtside
        simp [AspisR1.ExtractedMaskCoefficientLoop1.writeModel1]
  | succ fuel ih =>
      have hstartlt : iter.start.val < iter.end.val := by omega
      obtain ⟨iter1, hnext, hinc, hend1, _⟩ :=
        AspisR1.ExtractedMaskForwardRange.next_step iter hstartlt
      have hcolumn : iter.start.val < 10 := by omega
      have hend1' : iter1.end.val = 10 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 10 := by omega
      have hstart1 : iter1.start.val = iter.start.val + 1 := hinc
      have hnext' :
          core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
            .ok (some iter.start, iter1) := hnext
      have hwrite :=
        AspisR1.ExtractedMaskCoefficientWriteMeaning.decoded_writeAt1
          maskOnly initial iter.start hcolumn (by simpa using hsource ⟨iter.start.val, hcolumn⟩)
      let after := AspisR1.ExtractedMaskCoefficientLoop1.writeAt1
        maskOnly initial iter.start hcolumn
      have hmodel :
          AspisR1.ExtractedMaskCoefficientLoop1.writeModel1 maskOnly initial iter (fuel + 1) =
            AspisR1.ExtractedMaskCoefficientLoop1.writeModel1 maskOnly after iter1 fuel := by
        simp [AspisR1.ExtractedMaskCoefficientLoop1.writeModel1,
          hnext', hcolumn, after]
      have hih := ih after iter1 hend1' hspan1
      constructor
      · intro j hlow hhigh
        rw [hmodel]
        by_cases hj : j.val = iter.start.val
        · have hji : j = ⟨iter.start.val, hcolumn⟩ := Fin.ext hj
          have hnoFuture : ∀ k : Fin 10,
              iter1.start.val ≤ k.val → k.val < 10 → maskExponent k ≠ maskExponent j := by
            intro k hklo hkhigh heq
            have hkj : k.val = j.val := congrArg Fin.val (mask_schedule_injective heq)
            have hjv : j.val = iter.start.val := by simp [hji]
            omega
          have hkeep := hih.2 (maskExponent j) hnoFuture
          rw [hji, hwrite, Function.update_self] at hkeep
          simpa [maskMeaning, hji] using hkeep
        · have hjlo : iter1.start.val ≤ j.val := by omega
          exact hih.1 j hjlo hhigh
      · intro e houtside
        rw [hmodel]
        have hfirst : maskExponent ⟨iter.start.val, hcolumn⟩ ≠ e := by
          exact houtside ⟨iter.start.val, hcolumn⟩ (Nat.le_refl _) hcolumn
        have hnoFuture : ∀ j : Fin 10,
            iter1.start.val ≤ j.val → j.val < 10 → maskExponent j ≠ e := by
          intro j hjlo hjhi
          exact houtside j (by omega) hjhi
        have hkeep := hih.2 e hnoFuture
        rw [hwrite, Function.update_of_ne hfirst.symm] at hkeep
        exact hkeep

/-- Full-range actual loop-1 output inherits the mask-only schedule meaning.
Its initial array can contain the completed loop-0 cells; every coefficient
outside the ten mask-only destinations is preserved exactly. -/
theorem loop1_full_range
    (maskOnly : MaskOnly) (initial : Coefficients)
    (hsource : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))
    (hinitial : CanonicalArray initial) :
    ∃ out : Coefficients,
      state_only_hiding.state_only_selected_mask_value_loop1
        { start := 0#usize, «end» := 10#usize } maskOnly initial = .ok out ∧
      CanonicalArray out ∧
      (∀ j : Fin 10,
        AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients out
          (maskExponent j) = maskMeaning maskOnly j) ∧
      (∀ e : Fin 27,
        (∀ j : Fin 10, maskExponent j ≠ e) →
        AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients out e =
          AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients initial e) := by
  let iter : Range := { start := 0#usize, «end» := 10#usize }
  obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
    AspisR1.ExtractedMaskCoefficientLoop1.loop1_exec maskOnly iter initial 10 rfl (by rfl)
      hsource hinitial
  have hmeaning := loop1_model_interval maskOnly initial iter 10 rfl (by rfl) hsource
  refine ⟨out, ?_, hcanonical, ?_, ?_⟩
  · simpa [iter] using hrun
  · intro j
    have hj := hmeaning.1 j (Nat.zero_le _) j.isLt
    rw [hmodel]
    simpa [iter] using hj
  · intro e houtside
    have h := hmeaning.2 e (by
      intro j _ _
      exact houtside j)
    rw [hmodel]
    simpa [iter] using h

#print axioms loop0_model_interval
#print axioms loop1_model_interval
#print axioms loop0_full_range
#print axioms loop1_full_range

end AspisR1.ExtractedMaskCoefficientLoopMeaning
