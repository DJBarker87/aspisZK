import NFW_ErrorReferenceFuns
import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace AspisR1.NFW_ErrorReferenceEq
open Aeneas Aeneas.Std Result
def wire (e : NFW_ErrorReference.WireError) : AspisR1PublicPreparation.r1_wire.Error :=
 match e with
 | .Allocation=>.Allocation | .RowOrder a b=>.RowOrder a b | .InvalidRow=>.InvalidRow
 | .Tag row=>.Tag row | .Length row=>.Length row | .NonCanonical row n=>.NonCanonical row n
 | .Boundary n=>.Boundary n | .Terminal=>.Terminal | .EqualCirclePoints=>.EqualCirclePoints
 | .TrailingBytes=>.TrailingBytes | .Public=>.Public

def verifier (e : NFW_ErrorReference.VerifierError) : AspisR1PublicPreparation.verifier.Error :=
 match e with
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def result (r : core.result.Result Unit NFW_ErrorReference.WireError) :
 core.result.Result Unit AspisR1PublicPreparation.r1_wire.Error :=
 match r with | .Ok x=>.Ok x | .Err e=>.Err (wire e)

/-- Every raw u8/usize error payload is preserved, not just its variant. -/
theorem wire_injective : Function.Injective wire := by
 intro x y same
 cases x <;> cases y <;> simp_all [wire]

theorem prefix (e : NFW_ErrorReference.WireError) :
 (do let r←NFW_ErrorReference.prefix_error_ref e;ok (result r))=ok (.Err (wire e)) := rfl

theorem semantic (e : NFW_ErrorReference.WireError) :
 (do let r←NFW_ErrorReference.semantic_error_ref e;ok (verifier r))=
 ok AspisR1PublicPreparation.verifier.Error.Semantic := rfl

theorem split (k : Usize) :
 (do let r←NFW_ErrorReference.split_error_ref k;ok (r.map verifier))=
 ok (if k=10#usize then none else some AspisR1PublicPreparation.verifier.Error.Parse) := by
 unfold NFW_ErrorReference.split_error_ref
 split <;> rfl

theorem resume :
 (do let r←NFW_ErrorReference.resume_error_ref;ok (verifier r))=
 ok AspisR1PublicPreparation.verifier.Error.Checkpoint := rfl
#print axioms wire_injective
#print axioms prefix
#print axioms semantic
#print axioms split
#print axioms resume
end AspisR1.NFW_ErrorReferenceEq
