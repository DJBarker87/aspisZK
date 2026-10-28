import AspisR1SemanticInit28.Funs
import R1Z.ProverCommitWalk28
/-! The actual extracted semantic initializer, lifted into the shared machine.
The checked public-length rejection happens before its only digest read. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInit28
open Aeneas Aeneas.Std Result AspisR1SemanticInit28 ProverCommitStateLift28
abbrev NativeState (H : Type) := r1_wire.SemanticTranscript H

def start {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (token : H)
    (publicBytes : Slice U8) (root : Bytes32) :
    M (core.result.Result (NativeState H) r1_wire.Error) := do
  let length ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len publicBytes)
  match length with
  | .Err _ => pure (.Err .Public)
  | .Ok length =>
    let state ← effect token (Array.to_slice (Array.make 5#usize [r1_wire.DOMAIN,
      Array.to_slice (Array.make 1#usize [0#u8]),
      Array.to_slice (core.num.U32.to_le_bytes length),publicBytes,Array.to_slice root]))
    pure (.Ok ⟨state,token,0#u8⟩)

/-- All length-conversion failures, checked before the digest, are retained.
The source helper itself is unchanged and extracted, not an assumed callback. -/
theorem source {H : Type} (hash : aspis_core.digest.Digest32 H) (token : H)
    (publicBytes : Slice U8) (root : Bytes32) :
    r1_wire.SemanticTranscript.new hash token publicBytes root =
    start hash.digest token publicBytes root := by
  unfold r1_wire.SemanticTranscript.new start
  dsimp only []
  cases h : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len publicBytes) with
  | fail e => rfl
  | div => rfl
  | ok value =>
    cases value <;> rfl

/-- One machine now covers initialization and the complete formal walk;
the native outer walk-owner equality remains a separate obligation. -/
def walk {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M Bytes32) (publicBytes : Slice U8)
    (records : ProverCommitWalk28.Records) (variant : AspisR1SimControl21.transport.Variant) :
    M ProverCommitWalk28.Outcome := do
  let initial ← start effect () publicBytes records.c1_root
  match initial with
  | .Err _ => pure (ProverCommitWalk28.rejected (Array.repeat 32#usize 0#u8))
  | .Ok initial =>
    ProverCommitWalk28.continuation effect
      ⟨initial.state,(),initial.next_row⟩ records variant

theorem walk_effects (publicBytes : Slice U8) (records : ProverCommitWalk28.Records)
    (variant : AspisR1SimControl21.transport.Variant)
    (machine : ProverCommitLogged28.LoggedMachine) :
    walk (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      publicBytes records variant machine =
    walk (ProverCommitLogged28.dictionary ProverCommitControl28.reference)
      publicBytes records variant machine := by
  exact install _ _ (ProverCommitLogged28.logged_exact _ _ ProverCommitCoinCall27.call_exact)
    (fun e => walk (fun (_ : Unit) p => read e p) publicBytes records variant) machine

#print axioms source
#print axioms walk_effects
end R1Z.ProverCommitInit28
