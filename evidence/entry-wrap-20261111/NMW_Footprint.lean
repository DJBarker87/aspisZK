import NMW_Commands
set_option autoImplicit false
noncomputable section
namespace NMW_Footprint
open Aeneas Aeneas.Std Result AspisR1 NMW_Outcome NMW_FullDispatch
/-- The wrapper adds no account/borrow/return-data write or runtime event. -/
theorem first_outcome {A W E : Type} (children : Children A W E)
 (args : Args A) (before post : W) (reply : Reply) (history : List E)
 (domain : Hiq_ReleaseRoute.stage1 args.data)
 (child : children.first args before = .returned reply post history) :
 process children args before = .returned reply post history := by
 rw [process_first children args before domain,child]
/-- No hypothetical cleanup world is manufactured after a non-returning child. -/
theorem second_stopped {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) (reason : Stop) (history : List E)
 (domain : Hiq_ReleaseRoute.asq8 args.data)
 (child : children.second args before = .stopped reason history) :
 process children args before = .stopped reason history := by
 rw [process_second children args before domain,child]
/-- Arbitrary statement about the WHOLE child's outcome transfers, so the fold
retains frame, ownership/token and full Result facts without selecting fields.
This is a support eliminator; child outcome hypotheses never enter a root. -/
theorem first_property {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) (domain : Hiq_ReleaseRoute.stage1 args.data)
 (property : Outcome W E → Prop) (law : property (children.first args before)) :
 property (process children args before) := by
 rw [process_first children args before domain]
 exact law

theorem second_property {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) (domain : Hiq_ReleaseRoute.asq8 args.data)
 (property : Outcome W E → Prop) (law : property (children.second args before)) :
 property (process children args before) := by
 rw [process_second children args before domain]
 exact law
#print axioms first_outcome
#print axioms second_stopped
#print axioms first_property
#print axioms second_property
end NMW_Footprint
end
