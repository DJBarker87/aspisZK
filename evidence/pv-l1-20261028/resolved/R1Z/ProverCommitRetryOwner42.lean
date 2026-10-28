import R1Z.ProverCommitOwnerModel42
import R1Z.ProverCommitRetry34

/-! Selected 64-byte source owner installed in the existing retry control.
Nonce choices are public parameters, not fresh coins. Entropy precedes the
serializer; reservation and mask construction remain in the continuation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRetryOwner42
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
open ProverCommitOwnerBytes42 ProverCommitOwnerRun42 ProverCommitOwnerModel42
open ProverCommitLedger36
abbrev Secret := R0Z.FsStatement.OracleAnswer × ProverCommitPublicNonce40.Raw

def api (nonce : R0Z.FsStatement.OracleAnswer)
    (out : Except ProverCommitPublicNonce40.EntropyError ProverCommitPublicNonce40.Raw × State) :
    ProverCommitRetry34.Status Secret × State :=
  (match out.1 with | .error _ => .Err .Entropy | .ok raw => .Ok (nonce,raw),out.2)

def nativeEntropy (nonce : Nat → ProverCommitOwnerZero42.Bytes)
    (schedule : Schedule) (tape : Nat → owner.Raw) : ProverCommitRetry34.Entropy State Secret :=
  fun index s => do
    let (result,after) ← owner.generate (io schedule tape) (nonce index) s
    ok (api (block (nonce index)) (status result,after))

def modelEntropy (nonce : Nat → ProverCommitOwnerZero42.Bytes)
    (schedule : Schedule) (tape : Nat → owner.Raw) : ProverCommitRetry34.Entropy State Secret :=
  fun index s =>
    let (result,after) := ProverCommitPublicNonce40.generate (block (nonce index))
      schedule (fun n => raw (tape n)) s
    ok (api (block (nonce index)) (forget result,after))

theorem entropy_model (nonce : Nat → ProverCommitOwnerZero42.Bytes)
    (schedule : Schedule) (tape : Nat → owner.Raw) (index : Nat) (s : State) :
    nativeEntropy nonce schedule tape index s = modelEntropy nonce schedule tape index s := by
  simp only [nativeEntropy,generate_exact,bind_tc_ok]
  exact congrArg (fun out => ok (api (block (nonce index)) out))
    (generate_model (nonce index) schedule tape s)

/-- The selected source owner is composed through all eight attempts with
an unrestricted subsequent prover continuation. This is a source-control
transport; no correctness of that continuation is hidden in a premise. -/
theorem eight_model {Proof : Type} (nonce : Nat → ProverCommitOwnerZero42.Bytes)
    (schedule : Schedule) (tape : Nat → owner.Raw) (pub : ProverCommitDomain34.Source)
    (continuation : Secret → ProverCommitDomain34.SourceBytes → State →
      Result (ProverCommitRetry34.Status Proof × State)) (s : State) :
    ProverCommitRetry34.eight (ProverCommitRetry34.realAttempt pub
      (nativeEntropy nonce schedule tape) continuation) s =
    ProverCommitRetry34.eight (ProverCommitRetry34.realAttempt pub
      (modelEntropy nonce schedule tape) continuation) s := by
  have eq : nativeEntropy nonce schedule tape = modelEntropy nonce schedule tape :=
    funext fun index => funext (entropy_model nonce schedule tape index)
  rw [eq]

#print axioms entropy_model
#print axioms eight_model
end R1Z.ProverCommitRetryOwner42
