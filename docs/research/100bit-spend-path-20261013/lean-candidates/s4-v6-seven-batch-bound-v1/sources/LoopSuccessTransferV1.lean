import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsLoopSuccessTransferV1

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem loop_success_transfer {α β : Type}
    (newStep oldStep : α → Result (ControlFlow α β)) (measure : α → Nat)
    (htransfer : ∀ s flow, newStep s = .ok flow → oldStep s = .ok flow)
    (hdecrease : ∀ s s', newStep s = .ok (.cont s') → measure s' < measure s)
    : ∀ s out, Aeneas.Std.loop newStep s = .ok out →
      Aeneas.Std.loop oldStep s = .ok out := by
  intro s out
  induction hmeasure : measure s using Nat.strong_induction_on generalizing s out with
  | h m ih =>
    intro hnew
    rw [Aeneas.Std.loop.eq_def] at hnew
    cases hs : newStep s with
    | fail e => rw [hs] at hnew; cases hnew
    | div => rw [hs] at hnew; cases hnew
    | ok flow =>
      rw [hs] at hnew
      cases flow with
      | done value =>
        change Result.ok value = Result.ok out at hnew
        have hold := htransfer s (.done value) hs
        rw [Aeneas.Std.loop.eq_def, hold]
        change Result.ok value = Result.ok out
        exact hnew
      | cont s' =>
        change Aeneas.Std.loop newStep s' = Result.ok out at hnew
        have hlt := hdecrease s s' hs
        have hltm : measure s' < m := by omega
        have htail := ih (measure s') hltm s' out rfl hnew
        have hold := htransfer s (.cont s') hs
        rw [Aeneas.Std.loop.eq_def, hold]
        change Aeneas.Std.loop oldStep s' = Result.ok out
        exact htail


theorem loop_success_transfer_invariant {α β : Type}
    (newStep oldStep : α → Result (ControlFlow α β)) (measure : α → Nat)
    (Inv : α → Prop)
    (htransfer : ∀ s flow, newStep s = .ok flow → oldStep s = .ok flow)
    (hpreserve : ∀ s s', Inv s → newStep s = .ok (.cont s') → Inv s')
    (hdecrease : ∀ s s', Inv s → newStep s = .ok (.cont s') → measure s' < measure s)
    : ∀ s out, Inv s → Aeneas.Std.loop newStep s = .ok out →
      Aeneas.Std.loop oldStep s = .ok out := by
  intro s out
  induction hmeasure : measure s using Nat.strong_induction_on generalizing s out with
  | h m ih =>
    intro hinv hnew
    rw [Aeneas.Std.loop.eq_def] at hnew
    cases hs : newStep s with
    | fail e => rw [hs] at hnew; cases hnew
    | div => rw [hs] at hnew; cases hnew
    | ok flow =>
      rw [hs] at hnew
      cases flow with
      | done value =>
        have hold := htransfer s (.done value) hs
        rw [Aeneas.Std.loop.eq_def, hold]
        change Result.ok value = Result.ok out
        exact hnew
      | cont s' =>
        change Aeneas.Std.loop newStep s' = Result.ok out at hnew
        have hlt := hdecrease s s' hinv hs
        have hltm : measure s' < m := by omega
        have hinv' := hpreserve s s' hinv hs
        have htail := ih (measure s') hltm s' out rfl hinv' hnew
        have hold := htransfer s (.cont s') hs
        rw [Aeneas.Std.loop.eq_def, hold]
        change Aeneas.Std.loop oldStep s' = Result.ok out
        exact htail

#print axioms loop_success_transfer_invariant
#print axioms loop_success_transfer
end AspisR1FastDotsLoopSuccessTransferV1
