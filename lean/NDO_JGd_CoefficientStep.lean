import NDO_JGd_ExactWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_CoefficientStep
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Range := core.ops.range.Range Usize
abbrev Coeffs := ExtractedMaskCoefficientStep.Coefficients

theorem basis (x y : field.QM31) (i : Usize)
    (hx : ExtractedMaskTowerAdd.CanonicalQM x) (hi : i.val < 4)
    (hv : ExtractedMaskTowerBasis.basisWords (ExtractedMaskTowerAdd.wordsQM x) i.val =
      ExtractedMaskTowerAdd.wordsQM y) : state_only_hiding.mul_tower_basis x i = ok y := by
  obtain ⟨z,call,_,value⟩ := ExtractedMaskTowerBasis.current_mul_tower_basis_words x i hx hi
  have same : z=y := JFr_WordArithmetic.probe_words_injective (value.trans hv)
  exact same ▸ call

theorem next (a b c : Usize) (hlt : a.val < b.val) (hs : a.val+1=c.val) :
    Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize
      (⟨a,b⟩ : Range) = ok (some a,(⟨c,b⟩ : Range)) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step ⟨a,b⟩ hlt
  have sameStart : r.start=c := UScalar.eq_of_val_eq (start.trans hs)
  have same : r=(⟨c,b⟩ : Range) := by cases r; simp_all
  exact same ▸ call

theorem step0 (c1 : ExtractedMaskCoefficientStep.C1) (arr : Coeffs)
    (a b c : Usize) (n : Nat) (ha : a.val < 16)
    (hn : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize
      (⟨a,b⟩ : Range) = ok (some a,(⟨c,b⟩ : Range))) :
    ExtractedMaskCoefficientLoop0.writeModel0 c1 arr ⟨a,b⟩ (n+1) =
      ExtractedMaskCoefficientLoop0.writeModel0 c1
        (ExtractedMaskCoefficientLoop0.writeAt0 c1 arr a ha) ⟨c,b⟩ n := by
  rw [ExtractedMaskCoefficientLoop0.writeModel0,hn]
  simp only [dif_pos ha]

theorem step1 (m : ExtractedMaskCoefficientStep.MaskOnly) (arr : Coeffs)
    (a b c : Usize) (n : Nat) (ha : a.val < 10)
    (hn : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize
      (⟨a,b⟩ : Range) = ok (some a,(⟨c,b⟩ : Range))) :
    ExtractedMaskCoefficientLoop1.writeModel1 m arr ⟨a,b⟩ (n+1) =
      ExtractedMaskCoefficientLoop1.writeModel1 m
        (ExtractedMaskCoefficientLoop1.writeAt1 m arr a ha) ⟨c,b⟩ n := by
  rw [ExtractedMaskCoefficientLoop1.writeModel1,hn]
  simp only [dif_pos ha]
#print axioms basis
#print axioms next
#print axioms step0
#print axioms step1
end AspisR1.JGd_CoefficientStep
end
