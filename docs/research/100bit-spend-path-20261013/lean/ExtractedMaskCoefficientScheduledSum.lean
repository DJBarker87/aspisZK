import ExtractedMaskCoefficientSchedule
import Mathlib.Algebra.BigOperators.Fin

/-! Draft only: reindex a length-27 polynomial coefficient evaluation by the
actual two disjoint sparse schedules. The proof uses a finite equivalence and
symbolic sums; it does not expand coefficients or evaluate a recurrence. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCoefficientScheduledSum

open AspisR1.ExtractedMaskCoefficientArray
open AspisR1.ExtractedMaskCoefficientSchedule

abbrev ScheduleIndex := (Fin 16 ⊕ Fin 10) ⊕ PUnit

def exceptionIndex : Fin 27 := ⟨23, by omega⟩

def scheduleIndex : ScheduleIndex → Fin 27
  | Sum.inl (Sum.inl j) => c1Exponent j
  | Sum.inl (Sum.inr j) => maskExponent j
  | Sum.inr _ => exceptionIndex

private theorem c1_ne_exception (j : Fin 16) :
    c1Exponent j ≠ exceptionIndex := by
  intro h
  have hne := (schedules_cover_except_23 (c1Exponent j)).mp
    (Or.inl ⟨j, rfl⟩)
  have hv := congrArg Fin.val h
  exact hne (by simpa [exceptionIndex] using hv)

private theorem mask_ne_exception (j : Fin 10) :
    maskExponent j ≠ exceptionIndex := by
  intro h
  have hne := (schedules_cover_except_23 (maskExponent j)).mp
    (Or.inr ⟨j, rfl⟩)
  have hv := congrArg Fin.val h
  exact hne (by simpa [exceptionIndex] using hv)

private theorem scheduleIndex_injective : Function.Injective scheduleIndex := by
  intro a b hab
  cases a with
  | inl a =>
    cases a with
    | inl i =>
      cases b with
      | inl b =>
        cases b with
        | inl j =>
          change c1Exponent i = c1Exponent j at hab
          have hij := factor_schedule_injective hab
          exact congrArg Sum.inl (congrArg Sum.inl hij)
        | inr j => exact False.elim (schedules_disjoint i j hab)
      | inr unit => exact False.elim (c1_ne_exception i hab)
    | inr i =>
      cases b with
      | inl b =>
        cases b with
        | inl j => exact False.elim (schedules_disjoint j i hab.symm)
        | inr j =>
          change maskExponent i = maskExponent j at hab
          have hij := mask_schedule_injective hab
          exact congrArg Sum.inl (congrArg Sum.inr hij)
      | inr unit => exact False.elim (mask_ne_exception i hab)
  | inr unit =>
    cases b with
    | inl b =>
      cases b with
      | inl j => exact False.elim (c1_ne_exception j hab.symm)
      | inr j => exact False.elim (mask_ne_exception j hab.symm)
    | inr unit2 =>
      have : unit = unit2 := Subsingleton.elim _ _
      subst unit2
      rfl

private theorem scheduleIndex_surjective : Function.Surjective scheduleIndex := by
  intro e
  by_cases he : e.val = 23
  · refine ⟨Sum.inr PUnit.unit, ?_⟩
    apply Fin.ext
    simpa [scheduleIndex, exceptionIndex] using he.symm
  · have hc := (schedules_cover_except_23 e).mpr he
    rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨Sum.inl (Sum.inl j), by simpa [scheduleIndex] using hj⟩
    · exact ⟨Sum.inl (Sum.inr j), by simpa [scheduleIndex] using hj⟩

/-- The source schedule, together with the exceptional zero cell 23, is a
bijection with all 27 coefficient positions. -/
noncomputable def scheduleEquiv : ScheduleIndex ≃ Fin 27 :=
  Equiv.ofBijective scheduleIndex ⟨scheduleIndex_injective, scheduleIndex_surjective⟩

/-- Reindexing a weighted coefficient evaluation by the exact 16+10 schedule.
The only coefficient assumption is that the unfilled cell 23 is zero; `h₁`
and `h₂` identify values at the actual table destinations. -/
theorem weightedCoefficientSum_eq_scheduled
    {E : Type} [CommSemiring E]
    (coefficients : Fin 27 → E) (x : E)
    (c1Values : Fin 16 → E) (maskValues : Fin 10 → E)
    (h1 : ∀ j, coefficients (c1Exponent j) = c1Values j)
    (h2 : ∀ j, coefficients (maskExponent j) = maskValues j)
    (hzero : coefficients exceptionIndex = 0) :
    (∑ e : Fin 27, coefficients e * x ^ e.val) =
      (∑ j : Fin 16, c1Values j * x ^ (c1Exponent j).val) +
      ∑ j : Fin 10, maskValues j * x ^ (maskExponent j).val := by
  classical
  let term : Fin 27 → E := fun e => coefficients e * x ^ e.val
  calc
    (∑ e : Fin 27, coefficients e * x ^ e.val) =
        ∑ d : ScheduleIndex.{0}, term (scheduleIndex d) := by
      simpa [term, scheduleEquiv] using
        (Equiv.sum_comp scheduleEquiv term).symm
    _ =
      (∑ j : Fin 16, c1Values j * x ^ (c1Exponent j).val) +
        ∑ j : Fin 10, maskValues j * x ^ (maskExponent j).val := by
      have h23 : coefficients (23 : Fin 27) = 0 := by
        simpa [exceptionIndex] using hzero
      simp [term, scheduleIndex, exceptionIndex, h1, h2, h23]

#print axioms weightedCoefficientSum_eq_scheduled

end AspisR1.ExtractedMaskCoefficientScheduledSum
