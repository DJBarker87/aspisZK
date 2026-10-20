import CuSavingsCanonicalFieldStreamLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalFieldStreamCanonical
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalFieldStreamLoop
open CuSavingsCanonicalDotsField (WideCanonical)
variable [Shared]
theorem oldRun_success_canonical {S : Type} (next : S → Result (Option (E × K) × S))
    (canonical : ∀ cursor value scalar cursor1,
      next cursor=.ok (some (value,scalar),cursor1) → WideCanonical value)
    (cursor : S) (state : old_pairing.EbyKDot) (value : E)
    (h : oldRun next cursor state=.ok (.Ok value)) : WideCanonical value := by
  generalize hrank : 4097-state.count.val=rank
  induction rank using Nat.strong_induction_on generalizing cursor state with
  | h rank ih =>
    cases hn : next cursor with
    | fail e =>
      unfold oldRun at h
      rw [loop] at h
      simp only [body,hn,bind_tc_fail] at h
      cases h
    | div =>
      unfold oldRun at h
      rw [loop] at h
      simp only [body,hn,bind_tc_div] at h
      cases h
    | ok entry =>
      rcases entry with ⟨entry,cursor1⟩
      cases entry with
      | none =>
        unfold oldRun at h
        rw [source_none next _ _ cursor cursor1 _ hn,
          CuSavingsCanonicalDotsFinish.old_public_finish] at h
        have he := core.result.Result.Ok.inj (Result.ok.inj h)
        cases he
        exact CuSavingsCanonicalDotsFinish.result_canonical _ _
      | some pair =>
        rcases pair with ⟨input,scalar⟩
        have hc := canonical cursor input scalar cursor1 hn
        unfold oldRun at h
        rw [source_some next _ _ cursor cursor1 _ input scalar hn] at h
        cases hp : old_pairing.EbyKDot.push state input scalar with
        | fail e => rw [hp] at h;cases h
        | div => rw [hp] at h;cases h
        | ok entry =>
          rcases entry with ⟨result,state1⟩
          rw [hp] at h
          simp only [bind_tc_ok,uncurry_apply_pair] at h
          cases result with
          | Err e => cases h
          | Ok unit =>
            cases unit
            have hprogress := push_progress state state1 input scalar hc hp
            exact ih _ (by omega) cursor1 state1 h rfl
#print axioms oldRun_success_canonical
end AspisR1.CuSavingsCanonicalFieldStreamCanonical
