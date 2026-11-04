import NFG_SmallAssociation
import NEB_PureFrame
set_option autoImplicit false
namespace AspisR1.NFG_SmallEffects
open Aeneas Aeneas.Std Result
/-- Exact returned carrier and ambient persistent state/effects. -/
theorem neg {State Event : Type} (state : State) (x : NFG_SmallAssociation.CM) :
 NEB_PureFrame.run (Event:=Event) state
  (do let out ← NFG_SmallRefs.NFG_cm_ref x;ok (NFG_SmallAssociation.cm out)) =
 NEB_PureFrame.run state (AspisR72Sampler.field.CM31.neg (NFG_SmallAssociation.cm x)) :=
 NEB_PureFrame.equality state _ _ (NFG_SmallAssociation.neg x)
theorem zero {State Event : Type} (state : State) (x : NFG_SmallAssociation.QM) :
 NEB_PureFrame.run (Event:=Event) state (NFG_SmallRefs.NFG_qm_zero_ref x) =
 NEB_PureFrame.run state (AspisR72Sampler.field.QM31.is_zero (NFG_SmallAssociation.qm x)) :=
 NEB_PureFrame.equality state _ _ (NFG_SmallAssociation.zero x)
#print axioms neg
#print axioms zero
end AspisR1.NFG_SmallEffects
