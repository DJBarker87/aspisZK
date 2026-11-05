import NGM_ReferenceAcceptance
import NGM_FinishControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_ErrorCodec
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Error := verifier.Error
/-- Deployed Error discriminants, without host-only prover variants. -/
def encode : Error → U8
 | .Parse => 0#u8
 | .Semantic => 1#u8
 | .Transcript => 2#u8
 | .Relation => 3#u8
 | .Merkle => 4#u8
 | .Query => 5#u8
 | .Checkpoint => 6#u8
 | .Allocation => 7#u8

def decode (word : U8) : Option Error :=
 if word=0#u8 then some .Parse else
 if word=1#u8 then some .Semantic else
 if word=2#u8 then some .Transcript else
 if word=3#u8 then some .Relation else
 if word=4#u8 then some .Merkle else
 if word=5#u8 then some .Query else
 if word=6#u8 then some .Checkpoint else
 if word=7#u8 then some .Allocation else none

theorem roundtrip (error : Error) : decode (encode error)=some error := by
 cases error <;> rfl

theorem injective : Function.Injective encode := by
 intro a b equal
 have same := congrArg decode equal
 simpa only [roundtrip,Option.some.injEq] using same

def result : core.result.Result Unit Error → core.result.Result Unit U8
 | .Ok () => .Ok ()
 | .Err error => .Err (encode error)

theorem accepted_iff (reply : core.result.Result Unit Error) :
 result reply=.Ok () ↔ reply=.Ok () := by
 cases reply with
 | Ok unit => cases unit; simp [result]
 | Err error => simp [result]

#print axioms roundtrip
#print axioms injective
#print axioms accepted_iff
end AspisR1.NGM_ErrorCodec
end
