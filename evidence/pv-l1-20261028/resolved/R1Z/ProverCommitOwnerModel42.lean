import R1Z.ProverCommitOwnerRun42

/-! Projection to the existing two-private-block model, including every
rejected candidate and the complete history/cursor/ledger state. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnerModel42
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
open ProverCommitOwnerBytes42 ProverCommitLedger36 ProverCommitOwnerRun42
attribute [local instance] Classical.propDecidable
abbrev EntropyError := ProverCommitPublicNonce40.EntropyError

def status (r : NativeStatus) : Except EntropyError ProverCommitPublicNonce40.Raw :=
  match r with
  | .Err .RepeatedZero => .error .repeatedZero
  | .Err (.Os e) => .error (.os e)
  | .Ok secret => .ok (raw secret.raw)

def forget (r : Except EntropyError ProverCommitPublicNonce40.Private) :
    Except EntropyError ProverCommitPublicNonce40.Raw := r.map Subtype.val

theorem next_eq (schedule : Schedule) (tape : Nat → owner.Raw) (s : State) :
    ProverCommitPublicNonce40.next schedule (fun n => raw (tape n)) s =
      let (r,after) := ProverCommitOwnerRun42.next schedule tape s
      (match r with | .Err e => .error e | .Ok r => .ok (raw r),after) := by
  unfold ProverCommitPublicNonce40.next ProverCommitOwnerRun42.next
  cases step : ask schedule .rng s with
  | mk result after => cases result <;> rfl

theorem run_model (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule)
    (tape : Nat → owner.Raw) (n : Nat) (s : State) :
    let source := ProverCommitOwnerRun42.run nonce schedule tape n s
    let model := ProverCommitPublicNonce40.run schedule (fun n => raw (tape n)) n s
    (status source.1,source.2) = (forget model.1,model.2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitOwnerRun42.run,ProverCommitPublicNonce40.run,next_eq]
    cases step : ProverCommitOwnerRun42.next schedule tape s with
    | mk r after =>
      cases r with
      | Err e => rfl
      | Ok r =>
        dsimp only
        by_cases bad : block r.field=0 ∨ block r.leaf=0
        · have notgood : ¬ ∀ j, raw r j ≠ 0 := by rw [raw_good]; tauto
          simp only [bad,if_true,ProverCommitPublicNonce40.decode,dif_neg notgood]
          exact ih after
        · have good : ∀ j, raw r j ≠ 0 := by rw [raw_good]; tauto
          simp only [bad,if_false,ProverCommitPublicNonce40.decode,dif_pos good]
          rfl

theorem generate_model (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule)
    (tape : Nat → owner.Raw) (s : State) :
    let source := ProverCommitOwnerRun42.generate nonce schedule tape s
    let model := ProverCommitPublicNonce40.generate (block nonce) schedule (fun n => raw (tape n)) s
    (status source.1,source.2) = (forget model.1,model.2) := by
  simp only [ProverCommitOwnerRun42.generate,ProverCommitPublicNonce40.generate]
  by_cases hz : block nonce=0
  · simp only [hz,if_true]; rfl
  · simp only [hz,if_false]; exact run_model nonce schedule tape 16 s

#print axioms next_eq
#print axioms run_model
#print axioms generate_model
end R1Z.ProverCommitOwnerModel42
