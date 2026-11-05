import NID_ReadStepFrame
set_option autoImplicit false
noncomputable section
namespace NID_WithKTransport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem source {T : Type} (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (r : verifier.Reader)
 (left right : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T verifier.Error))
 (bound : r.at.val+16≤r.bytes.val.length)
 (same : ∀ q out, CheckpointBytes3Reader.readK r=ok (.Ok q,out) → left q out=right q out) :
 CheckpointBytes4Ops.withK (T2Nat_ScalarJoin.readK unwrap) r left=
 CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r right := by
 unfold CheckpointBytes4Ops.withK
 rw [NID_BoundedReaders.k unwrap unwrap_ok r bound]
 apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
 intro pair called
 rcases pair with ⟨value,out⟩
 cases value with
 | Err e => rfl
 | Ok q => exact same q out called
#print axioms source
end NID_WithKTransport
