import NMD_SegmentFold
import NLW_064CandidateFold
set_option autoImplicit false
noncomputable section
namespace NMD_CandidateFold
open Aeneas Aeneas.Std VTop_Stages AspisR1 NLW_Full064 NMD_CutState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The corrected merged 065 candidate discharges only the child RowSpec.
The Segments premise is explicit and has no actual-native producer yet.
This is support, not TX2:064's candidate root. -/
theorem fold {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (publicBound : s.frame.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.frame.args.checkpoint s.frame.args.proof)
 (outcome : End H s.frame.args) (events : List (Event Ambient X))
 (segments : NMD_SegmentFold.Segments H s outcome events) :
 Law H s.frame.args outcome ∧ events=chronology H s.frame outcome :=
 NMD_SegmentFold.fold H (NLW_064CandidateFold.child H) s publicBound root0 outcome events segments
#print fold
#print axioms fold
end NMD_CandidateFold
