import R1Z.RealR1_ReachableRetry

/-! P6 boundary: RealR1_client::prove_for_proof_accounts, the verbatim native
retry owner, and the selected 64-byte factory are checked against owned control.
This module instantiates the extracted structural retry with that factory and
reservation continuation. It does not assert the R2/R3 body contract or E1's
random marginal. Public account selection is an environment input; effects of
arbitrary client key-generation code are outside this function's control. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR1_ClientBinding
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
open ProverCommitRetry34 RealR1_OuterOwner RealR1_ReachableRetry

private def encode {S P : Type} : Step P × S → AspisR1Retry34.owner.Step P S ProverCommitRetry34.Error
  | (.done p,s) => .Done p s
  | (.retry,s) => .Retry s
  | (.stop e,s) => .Stop e s

def ops {S P : Type} (attempt : Attempt S P) : AspisR1Retry34.owner.Attempt Unit S P ProverCommitRetry34.Error where
  attempt := fun i s => do
    let pair ← attempt i.val s
    ok (encode pair)

theorem native_step {S P : Type} (attempt : Attempt S P) (i : Nat) (hi : i < 8) (s : S) :
    ProverCommitRetrySource34.policy (ops attempt) i s = attempt i s := by
  have size : 8 < UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  have hv : (ProverCommitRetrySource34.word i).val = i := by
    simp only [ProverCommitRetrySource34.word,UScalar.val,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa only [UScalar.size_def] using (show i < UScalar.size .Usize by omega))
  dsimp only [ProverCommitRetrySource34.policy, ops]
  rw [hv]
  cases h : attempt i s with
  | fail e => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨step,after⟩; cases step <;> rfl

/-- Extracted owned retry, with complete state at every boundary. -/
def client {Extra Proof : Type} (pub : Pub) (nonce : NoncePolicy Extra)
    (schedule : ProverCommitLedger36.Schedule) (tape : Nat → owner.Raw)
    (unix : Bool) (pre : Prefix Extra) (body : Body Extra Proof) (s : Store Extra) : Result (Step (Published Proof) × Store Extra) := do
  let result ← AspisR1Retry34.owner.retry
    (ops (realAttempt pub (nativeEntropy nonce schedule tape) (reserved pre schedule unix body)))
    8#usize 0#usize s
  ok (ProverCommitRetrySource34.decodeRun result)

theorem client_control {Extra Proof : Type} (pub : Pub) (nonce : NoncePolicy Extra)
    (schedule : ProverCommitLedger36.Schedule) (tape : Nat → owner.Raw)
    (unix : Bool) (pre : Prefix Extra) (body : Body Extra Proof) (s : Store Extra) :
    client pub nonce schedule tape unix pre body s =
      selected true pub (nativeEntropy nonce schedule tape) (reserved pre schedule unix body) s := by
  unfold client
  rw [ProverCommitRetrySource34.eight_source]
  exact run_reachable _ _ (fun _ _ => True)
    (fun i state bound _ => native_step _ i bound state)
    (fun _ _ _ _ _ _ => True.intro) 8 0 s (by omega) True.intro

/-- Native caller control joined to the model preparation/retry owner, with
only the reachable post-reservation R2/R3 body and invariant premises. The
public prefix instance, E1/E2 and the fixed experiment mapping remain visible
source/experiment obligations; no probability claim follows from this equality. -/
theorem client_outer {Extra Proof : Type} (pub : Pub) (nonce : NoncePolicy Extra)
    (schedule : ProverCommitLedger36.Schedule) (tape : Nat → owner.Raw)
    (unix : Bool) (pre : Prefix Extra) (Inv : Nat → Store Extra → Prop)
    (left right : Body Extra Proof)
    (contract : PreparedBodyContract pub (modelEntropy nonce schedule tape) pre schedule unix Inv left right)
    (advance : ∀ index s after, index < 8 → Inv index s →
      realAttempt pub (modelEntropy nonce schedule tape) (reserved pre schedule unix right)
        index s = ok (.retry,after) → Inv (index+1) after)
    (s : Store Extra) (initial : Inv 0 s) :
    client pub nonce schedule tape unix pre left s =
      selected true pub (modelEntropy nonce schedule tape) (reserved pre schedule unix right) s := by
  rw [client_control]
  exact outer_owner_reachable pub nonce schedule tape unix pre Inv left right contract advance s initial

#print axioms native_step
#print axioms client_control
#print axioms client_outer
end R1Z.RealR1_ClientBinding
