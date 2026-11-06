import NLJ_PrepareFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
def initial {H : Type} (i : Input H) : State H := ⟨i,.allocate⟩
/-- UNPROVED goal, not a hypothesis in an admitted root. Native state/owned/
abort realization and the exact137/179 caller packet installation are separate. -/
def SourceEquality (cfg : Configuration) {H : Type} (i : Input H) : Prop :=
 run (fold cfg 12 (initial i)) =
 run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std i.digest i.publicValue i.proof i.hash i.scratch)
#print SourceEquality
end AspisR1.NLJ_Prepare
end
