import R1Z.PV_RunJoin_CallerWorld
import R1Z.ProverRwRetryModel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceBinding
open Aeneas Aeneas.Std Result
variable [ProverRwFull.ExternalTypes]
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

/-- The verifier error constructors are all retained, not collapsed into a
success flag. Native getrandom errors are mapped by the selected callback. -/
def error : ProverRwRngCaller.Error → ProverRwFull.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation
  | .Rejected => .Rejected
  | .AttemptsExhausted => .AttemptsExhausted
  | .Entropy => .Entropy

def secret (s : ProverRwRngCaller.StateOnlyAttemptSecrets) : ProverRwRetryModel.Secret :=
  ⟨s.mask_nonce,s.field_mask_entropy,s.leaf_salt_seed⟩

/-- Source representations and the remaining source leaves are DATA. The
pointwise body equation below is a separate Prop, not part of this definition.
The source dictionary is indexed by the current native body/ledger world;
entropy is handled by the stateful caller, never by this pure dictionary. -/
structure BodyData (L B : Type) where
  ops : B → L → ProverRwFull.ExternalFuns
  pub : B → ProverRwRetryModel.Pub
  compiled : B → ProverRwRetryModel.Compiled
  hash : B → ProverRwRetryModel.Hash
  store : L → ProverRwRetryModel.Store
  audit : B → U64 → ProverRwFull.prover.MaskedFixtureAudit

def status {L B : Type} (d : BodyData L B) (after : B) :
    core.result.Result (alloc.vec.Vec U8 × U64) ProverRwRngCaller.Error →
      core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error
  | .Ok (proof,audit) => .Ok (proof,d.audit after audit)
  | .Err e => .Err (error e)

def output {L B : Type} (d : BodyData L B)
    (out : (L × core.result.Result (alloc.vec.Vec U8 × U64) ProverRwRngCaller.Error) × B) :=
  (status d out.2 out.1.2,d.store out.1.1)

/-- Exact residual successful/error BODY association at the source emission,
including the native MaskedFixtureAudit representation. This alone does not
associate changes to B with oracle events or L with the external filesystem. -/
def BodySourceLaw {L B : Type} (d : BodyData L B) (body : ProverRwRngCallerControl.Body B L) : Prop :=
  ∀ b l s,
    ProverCommitSemanticTransport26.mapR (output d) (body.call_mut b (s,l)) =
      letI : ProverRwFull.ExternalFuns := d.ops b l
      ProverRwFull.prover.prove_masked_attempt (d.pub b) (d.compiled b) .S2
        (d.hash b) (secret s) (d.store l)

theorem error_injective : Function.Injective error := by
  intro a b same
  cases a <;> cases b <;> cases same <;> rfl

theorem secret_nonce (s : ProverRwRngCaller.StateOnlyAttemptSecrets) :
    (secret s).mask_nonce = s.mask_nonce := rfl

#print axioms error
#print axioms secret
#print axioms status
#print axioms output
#print axioms BodySourceLaw
#print axioms error_injective
#print axioms secret_nonce
end R1Z.PV_RunJoin_SourceBinding
