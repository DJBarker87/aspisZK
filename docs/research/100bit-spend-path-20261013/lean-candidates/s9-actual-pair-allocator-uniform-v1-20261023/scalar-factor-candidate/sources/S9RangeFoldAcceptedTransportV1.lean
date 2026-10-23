import RangeFoldP6ModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RangeFoldAcceptedTransportV1
open AspisR1S3S9RangeFoldP6

theorem range_fold_success_transport {A B : Type}
    (map : A → B) (inv : A → Prop)
    (sourceStep : A → Usize → Result A) (targetStep : B → Usize → Result B)
    (hstep : ∀ state i next, inv state → sourceStep state i = .ok next →
      inv next ∧ targetStep (map state) i = .ok (map next)) :
    ∀ (fuel : Nat) (range : R) (state out : A), inv state →
      rangeFoldRun fuel range sourceStep state = .ok out →
      inv out ∧ rangeFoldRun fuel range targetStep (map state) = .ok (map out) := by
  intro fuel
  induction fuel with
  | zero =>
    intro range state out hi h
    change Result.ok state = Result.ok out at h
    cases Result.ok.inj h
    exact ⟨hi,rfl⟩
  | succ fuel ih =>
    intro range state out hi h
    simp only [rangeFoldRun] at h
    cases hr : rangeNext range with
    | fail e => simp only [hr,bind_tc_fail] at h; cases h
    | div => simp only [hr,bind_tc_div] at h; cases h
    | ok pair =>
      rcases pair with ⟨opt,rangeNext⟩
      cases opt with
      | none =>
        simp only [hr,bind_tc_ok] at h
        have ho : state = out := Result.ok.inj h
        subst out
        refine ⟨hi,?_⟩
        simp only [rangeFoldRun,hr,bind_tc_ok]
      | some i =>
        simp only [hr,bind_tc_ok] at h
        cases hs : sourceStep state i with
        | fail e => simp only [hs,bind_tc_fail] at h; cases h
        | div => simp only [hs,bind_tc_div] at h; cases h
        | ok next =>
          simp only [hs,bind_tc_ok] at h
          obtain ⟨hinext,htarget⟩ := hstep state i next hi hs
          obtain ⟨hiout,hrest⟩ := ih rangeNext next out hinext h
          refine ⟨hiout,?_⟩
          simp only [rangeFoldRun,hr,bind_tc_ok,htarget]
          exact hrest

#print axioms range_fold_success_transport
end AspisR1S9RangeFoldAcceptedTransportV1
