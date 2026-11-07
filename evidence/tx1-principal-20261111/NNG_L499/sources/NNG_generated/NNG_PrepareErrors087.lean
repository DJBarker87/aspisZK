import NNG_PrepareCarriers087
import LIBC_ExpandValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareErrors087
open Aeneas Aeneas.Std NMP_prepare

def error : verifier.Error → LIB_VCarriers.VErr
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation
def errorBack : LIB_VCarriers.VErr → verifier.Error
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation
theorem error_inverse (e : verifier.Error) : errorBack (error e)=e := by cases e <;> rfl
theorem errorBack_inverse (e : LIB_VCarriers.VErr) : error (errorBack e)=e := by cases e <;> rfl

def codec : compact.CodecError → LIB_VCarriers.CodecErr
 | .Length=>.Length | .NonZeroHigh=>.NonZeroHigh | .NonCanonical=>.NonCanonical
def codecBack : LIB_VCarriers.CodecErr → compact.CodecError
 | .Length=>.Length | .NonZeroHigh=>.NonZeroHigh | .NonCanonical=>.NonCanonical
theorem codec_inverse (e : compact.CodecError) : codecBack (codec e)=e := by cases e <;> rfl
theorem codecBack_inverse (e : LIB_VCarriers.CodecErr) : codec (codecBack e)=e := by cases e <;> rfl
#print axioms error_inverse
#print axioms errorBack_inverse
#print axioms codec_inverse
#print axioms codecBack_inverse
end AspisR1.NNG_PrepareErrors087
