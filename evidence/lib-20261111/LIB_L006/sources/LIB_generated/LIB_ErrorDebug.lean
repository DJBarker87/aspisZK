import LIB_Carriers
import NIS_ErrorJoin
import NMS_R2ErrorSource
import NMN_064
set_option autoImplicit false
noncomputable section
namespace LIB_ErrorDebug
open Aeneas Aeneas.Std
/-- One verifier error carrier, shared by both verifier libraries. -/
abbrev VErr := VTop_Stages.verifier.Error
def adapter : VErr → NGL_ErrorModel.E
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def fromAdapter : NGL_ErrorModel.E → VErr
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def debug (e : VErr) : String := NGL_ErrorModel.label (adapter e)
theorem adapter_back (e : VErr) : fromAdapter (adapter e) = e := by cases e <;> rfl
theorem adapter_forth (e : NGL_ErrorModel.E) : adapter (fromAdapter e) = e := by cases e <;> rfl
theorem native_format (e : VErr) :
    NIJ_ErrorJoin.formatted (adapter e) = "r1:error:" ++ debug e := NIJ_ErrorJoin.bytes _
/-- CLOSED TX2:211 / TX1:NGB001, including the stopped logging arms.
The formatter allocation is kept separately by NMS_R2ErrorSource. -/
theorem native_source {S : Type} (emit : String → S → Result S) (e : VErr) (s : S) :
    NIJ_ErrorJoin.run emit (adapter e) s = do
      let after ← emit ("r1:error:" ++ debug e) s
      .ok (AdapterRw.solana_program_error.ProgramError.InvalidInstructionData, after) :=
  NIJ_ErrorJoin.source emit (adapter e) s
#print axioms adapter_back
#print axioms adapter_forth
#print axioms native_format
#print axioms native_source
end LIB_ErrorDebug
