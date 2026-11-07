import NMK_Domain
import NMD_ComputedFold
set_option autoImplicit false
noncomputable section
namespace NMK_CompleteFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064 NMD_CutState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- A conditional fold, never a row root. The native producer is explicit;
no successful-child assumption or return is fabricated on the stopped arm. -/
theorem fold {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical) (domain : NMK_Domain.Caller s.frame.args)
 (outcome : End H s.frame.args) (events : List (Event Ambient X))
 (producer : Invocation H s.frame outcome events) :
 Law H s.frame.args outcome ∧ events = chronology H s.frame outcome := by
 exact NLW_064CandidateFold.fold H s.frame domain.publicBound
  ((NLW_RowSpec_065.root0_same _ _).mpr domain.root0) outcome events producer
/-- Literal equality to the selected-child transcription, retaining all G
arms. The producer and selection are certification obligations, not trust rows. -/
theorem selected {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash)
 (outcome : End H s.frame.args) (events : List (Event Ambient X))
 (producer : Invocation H s.frame outcome events)
 (same : NMD_ComputedFold.Selected H s pick outcome) :
 (outcome,events) = NMD_ComputedFold.run H s pick :=
 NMD_ComputedFold.same_fold H s pick outcome events producer same
#print fold
#print selected
#print axioms fold
#print axioms selected
end NMK_CompleteFold
