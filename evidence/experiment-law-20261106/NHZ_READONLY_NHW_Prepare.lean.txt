import NHS_NewPort
import NHL_PrepareModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The emitted constructor packet, not an arbitrary constructor result. -/
def nativeChildren (base : Ops) : Ops := {base with op8:=@NHS_NewPort.emitted}
/-- Instantiates NHL's full-Result constructor hypothesis. The semantic
verification law is the sole remaining model child equation. Native prefix
association remains separate and is not asserted by this theorem. -/
theorem source (base : Ops) (reserved : Bool)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (g : NHL_PrepareStages.Scratch)
 (verify_observed : ∀ v, NHL_PrepareModel.Reaches (nativeChildren base) reserved D proof v →
   base.op9 D pub v.semantic hash none=
   (RowShape_InstalledSlots.verifierOps base B std).op9 D pub v.semantic hash none) :
 NHL_EmittedPrepare.prepare (NHL_Packets.installed (nativeChildren base) reserved)
   D pub proof hash none g=
 verifier.candidate.prepare
   (NHL_PrepareModel.children (NHL_Packets.installed (nativeChildren base) reserved)
     (RowShape_InstalledSlots.verifierOps base B std)) D pub proof hash none g := by
 apply NHL_PrepareModel.source
 · exact verify_observed
 · intro v sem _ _
   exact NHS_NewPort.slot base B std D sem v hash g
#print axioms source
end AspisR1.NHW_Prepare
