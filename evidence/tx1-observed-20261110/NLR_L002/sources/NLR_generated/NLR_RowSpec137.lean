import NLJ_ControlFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Interface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
structure ExternalFrame where
 bytes : Nat → List U8
 metadata : Nat → List Nat
 authorities : Nat → List U8
structure Observation137 where
 afterInput : NLJ_Observed.Input Unit
 afterFrame : ExternalFrame
 reply : Result (NLJ_Observed.Out Unit)
 log : PreparedHashCode.Log
 events : List NLJ_Observed.Event
abbrev Native137 := NLJ_Observed.Input Unit → ExternalFrame → Observation137
/-- Draft FULL packet under (be)(1), not a native realization. The actual
producer must be fixed by the reviewed physical cuts. Own argument domain
is byte extent13831; every caller must establish it under (bf). All inner
errors, outer abort/divergence and attempted effects are retained. -/
def RowSpec_137 (native : Native137) : Prop :=
 ∀ (i : NLJ_Observed.Input Unit) (before : ExternalFrame),
 i.bytes.val.length = 13831 →
 (native i before).afterInput = i ∧
 (native i before).afterFrame = before ∧
 NLJ_Observed.Invocation 6 (NLJ_Observed.initial i)
  (native i before).reply (native i before).log (native i before).events ∧
 PreparedHashCode.run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) =
  ((native i before).log,(native i before).reply)
#print RowSpec_137
end AspisR1.NLR_Interface
end
