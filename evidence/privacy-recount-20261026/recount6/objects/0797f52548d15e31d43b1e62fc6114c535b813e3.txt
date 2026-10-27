import R1Z.ProverCommitOwnedDecoder
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result
open R1Z.ProverCommitFourSteps (collect)
open R1Z.ProverCommitStepLoop (State Hash Sample)

theorem collect_length {S : Type} (step : S → Result (Sample × S))
    (n : Nat) (s final : S) (values : List U32)
    (success : collect step n s = ok (.Ok values, final)) : values.length = n := by
  induction n generalizing s final values with
  | zero =>
    simp only [collect] at success
    cases success
    rfl
  | succ n ih =>
    simp only [collect] at success
    cases hs : step s with
    | fail e => simp only [hs, bind_tc_fail] at success; contradiction
    | div => simp only [hs, bind_tc_div] at success; contradiction
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [hs, bind_tc_ok, Aeneas.Std.uncurry_apply_pair] at success
      cases sample with
      | Err e => cases success
      | Ok a =>
        cases ht : collect step n after with
        | fail e => simp only [ht, bind_tc_fail] at success; contradiction
        | div => simp only [ht, bind_tc_div] at success; contradiction
        | ok pair =>
          rcases pair with ⟨tail, last⟩
          simp only [ht, bind_tc_ok] at success
          cases tail with
          | Err e => cases success
          | Ok vs =>
            cases success
            exact congrArg Nat.succ (ih after _ vs ht)

theorem samples_length (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : List U32) (success : samples hash domain n = some values) :
    values.length = n := by
  unfold samples at success
  cases h : collect (AspisR1ProverStep8.prover_commit_reference.limb_caller hash domain)
      n initial with
  | fail e => simp only [h, reduceCtorEq] at success
  | div => simp only [h, reduceCtorEq] at success
  | ok pair =>
    rcases pair with ⟨sample, final⟩
    cases sample with
    | Err e => simp only [h, reduceCtorEq] at success
    | Ok vs =>
      simp only [h, Option.some.injEq] at success
      subst values
      exact collect_length _ n initial final vs h

/-- No successful operational sample lookup uses the default zero. -/
theorem samples_index (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : List U32) (success : samples hash domain n = some values) (i : Fin n) :
    values[i.val]?.getD 0#u32 = values[i.val]'(by rw [samples_length hash domain n values success]; exact i.isLt) := by
  rw [List.getElem?_eq_getElem (by rw [samples_length hash domain n values success]; exact i.isLt)]
  rfl

#print axioms collect_length
#print axioms samples_length
#print axioms samples_index
end R1Z.ProverCommitOwnedDecoder
