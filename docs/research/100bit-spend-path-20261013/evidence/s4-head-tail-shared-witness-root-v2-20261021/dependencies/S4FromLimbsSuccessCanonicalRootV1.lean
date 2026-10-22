import S4ConcreteTailInstallRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFromLimbsSuccessCanonicalRootV1

private theorem bind_success {A B : Type} (r : Result A) (f : A → Result B)
    (y : B) (h : Bind.bind r f = .ok y) :
    ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

abbrev FinishWide := AspisR1EbyKFinish.field.wide_exact.WideExact
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact

def CanonicalParts (x : FinishWide) : Prop :=
  x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647 ∧
  x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647 ∧
  x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647 ∧
  x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647

/-- Every successful actual parser return passed all eight canonical checks.
No canonicality premise is imposed on the input array. -/
theorem actual_from_limbs_success_canonical
    (xs : Array U32 8#usize) (out : FinishWide)
    (h : AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs xs = .ok (some out)) :
    CanonicalParts out := by
  unfold AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs at h
  obtain ⟨w0, _hread0, h⟩ := bind_success _ _ _ h
  by_cases hc0 : w0 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc0] at h
    cases h
  rw [if_neg hc0] at h
  obtain ⟨w1, _hread1, h⟩ := bind_success _ _ _ h
  by_cases hc1 : w1 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc1] at h
    cases h
  rw [if_neg hc1] at h
  obtain ⟨w2, _hread2, h⟩ := bind_success _ _ _ h
  by_cases hc2 : w2 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc2] at h
    cases h
  rw [if_neg hc2] at h
  obtain ⟨w3, _hread3, h⟩ := bind_success _ _ _ h
  by_cases hc3 : w3 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc3] at h
    cases h
  rw [if_neg hc3] at h
  obtain ⟨w4, _hread4, h⟩ := bind_success _ _ _ h
  by_cases hc4 : w4 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc4] at h
    cases h
  rw [if_neg hc4] at h
  obtain ⟨w5, _hread5, h⟩ := bind_success _ _ _ h
  by_cases hc5 : w5 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc5] at h
    cases h
  rw [if_neg hc5] at h
  obtain ⟨w6, _hread6, h⟩ := bind_success _ _ _ h
  by_cases hc6 : w6 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc6] at h
    cases h
  rw [if_neg hc6] at h
  obtain ⟨w7, _hread7, h⟩ := bind_success _ _ _ h
  by_cases hc7 : w7 >= AspisR1EbyKFinish.field.P
  · rw [if_pos hc7] at h
    cases h
  rw [if_neg hc7] at h
  have hout := Option.some.inj (Result.ok.inj h)
  subst out
  unfold CanonicalParts
  have hb0 : w0.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc0
    change ¬ 2147483647 ≤ w0.val at hc0
    omega
  have hb1 : w1.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc1
    change ¬ 2147483647 ≤ w1.val at hc1
    omega
  have hb2 : w2.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc2
    change ¬ 2147483647 ≤ w2.val at hc2
    omega
  have hb3 : w3.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc3
    change ¬ 2147483647 ≤ w3.val at hc3
    omega
  have hb4 : w4.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc4
    change ¬ 2147483647 ≤ w4.val at hc4
    omega
  have hb5 : w5.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc5
    change ¬ 2147483647 ≤ w5.val at hc5
    omega
  have hb6 : w6.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc6
    change ¬ 2147483647 ≤ w6.val at hc6
    omega
  have hb7 : w7.val < 2147483647 := by
    unfold AspisR1EbyKFinish.field.P at hc7
    change ¬ 2147483647 ≤ w7.val at hc7
    omega
  exact ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7⟩

theorem finish_to_current_canonical (x : FinishWide) (hx : CanonicalParts x) :
    AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE
        (AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent x)) := by
  rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

/-- The explicit parser installation discharges the callback body's
canonicality contract on every accepted input. -/
theorem installed_from_limbs_success_canonical
    (base : AspisR1FastDotsCurrent.FourDotsOps)
    (xs : Array U32 8#usize) (out : Wide)
    (h : (AspisR1FastDotsConcreteTailInstallRootV1.install base).wideFromLimbs xs =
      .ok (some out)) :
    AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) := by
  change AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent xs = .ok (some out) at h
  unfold AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent at h
  obtain ⟨parsed,hparsed,h⟩ := bind_success _ _ _ h
  cases parsed with
  | none => cases h
  | some x =>
    have hout := Option.some.inj (Result.ok.inj h)
    subst out
    exact finish_to_current_canonical x (actual_from_limbs_success_canonical xs x hparsed)

#print axioms actual_from_limbs_success_canonical
#print axioms finish_to_current_canonical
#print axioms installed_from_limbs_success_canonical
end AspisR1FastDotsFromLimbsSuccessCanonicalRootV1
