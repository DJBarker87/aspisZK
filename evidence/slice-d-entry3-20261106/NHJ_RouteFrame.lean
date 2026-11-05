import NHJ_RoutePacket
set_option autoImplicit false
noncomputable section
namespace NHJ_RouteFrame
open Aeneas Aeneas.Std Result
open AspisR1

def prefix4 (data : Slice U8) : Slice U8 :=
  ⟨data.val.take 4, by
    rw [List.length_take]
    exact (Nat.min_le_right 4 data.val.length).trans data.property⟩

private theorem not_two (data : Slice U8) (large : 4 ≤ data.val.length) :
    ¬ Hiq_ReleaseRoute.stage1 data := by
  intro selected
  rcases selected with selected | selected
  all_goals
    have length := congrArg List.length selected
    simp only [List.length_cons,List.length_nil] at length
    omega

theorem four_length (data : Slice U8) (large : 4 ≤ data.val.length) :
    (prefix4 data).val.length = 4 := by
  simp only [prefix4,List.length_take,Nat.min_eq_left large]

/-- Full suffix frame for the actual adopted classifier. No bound on the
whole input length, parent acceptance, or supplied output equality appears. -/
theorem four_window (data : Slice U8) (large : 4 ≤ data.val.length) :
    Hiq_DispatchSource.pool_route.admitted data =
      Hiq_DispatchSource.pool_route.admitted (prefix4 data) := by
  classical
  rw [Hiq_DispatchAdmitted.exact,Hiq_DispatchAdmitted.exact]
  have original := not_two data large
  have shortened := not_two (prefix4 data) (by rw [four_length data large])
  simp only [Hiq_ReleaseRoute.stage1,Hiq_ReleaseRoute.asq8] at original shortened ⊢
  change ¬ (data.val.take 4 = [3#u8,10#u8] ∨ data.val.take 4 = [3#u8,11#u8]) at shortened
  simpa [original,shortened,prefix4,List.take_take]

theorem rejected_short (data : Slice U8) (short : data.val.length < 4)
    (notTwo : data.val.length ≠ 2) :
    Hiq_DispatchSource.pool_route.admitted data = ok false := by
  rw [NHJ_RoutePacket.cohort]
  simp [NHJ_RoutePacket.observed,NHJ_RoutePacket.header,notTwo,Nat.not_le.mpr short]
#print axioms four_length
#print axioms four_window
#print axioms rejected_short
end NHJ_RouteFrame
