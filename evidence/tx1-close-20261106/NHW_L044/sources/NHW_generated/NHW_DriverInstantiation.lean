import NHW_EmittedEq
import NHL_DriverModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_DriverInstantiation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Interpret the already bridged callees. This is a model dictionary;
native argument/frame association and caller-domain proofs stay separate. -/
def packetOps (base expected : Ops) : Ops :=
 {NHW_Prepare.nativeChildren base with op7:=expected.op7,op16:=expected.op16,op17:=expected.op17}
/-- Instantiates every NHL model child except verify_observed. There is no
successful prepare/query/checkpoint premise; failures keep their full Result.
This theorem alone does not certify native packet installation. -/
theorem source (base : Ops) (reserved : Bool)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H)
 (verify_observed : ∀ v,
   NHL_PrepareModel.Reaches (packetOps base (RowShape_InstalledSlots.verifierOps base B std)) reserved D proof v →
   base.op9 D pub v.semantic hash none=(RowShape_InstalledSlots.verifierOps base B std).op9 D pub v.semantic hash none) :
 NHW_EmittedTx1.tx1
   (NHL_Packets.installed (packetOps base (RowShape_InstalledSlots.verifierOps base B std)) reserved)
   (NHW_EmittedPrepare.prepare
     (NHL_Packets.installed (packetOps base (RowShape_InstalledSlots.verifierOps base B std)) reserved))
   D pub publicBytes proof k hash none=
 verifier.candidate.tx1
   (NHL_DriverModel.txOps (packetOps base (RowShape_InstalledSlots.verifierOps base B std))
      (RowShape_InstalledSlots.verifierOps base B std) reserved)
   D pub publicBytes proof k hash none := by
 rw [NHW_EmittedEq.tx1]
 have first : (NHW_EmittedPrepare.prepare
     (NHL_Packets.installed (packetOps base (RowShape_InstalledSlots.verifierOps base B std)) reserved) : NHL_EmittedTx1.Prepare H)=
   NHL_EmittedPrepare.prepare (NHL_Packets.installed (packetOps base (RowShape_InstalledSlots.verifierOps base B std)) reserved) := by
   funext d p pr h o g
   exact NHW_EmittedEq.prepare _ d p pr h o g
 rw [first]
 apply NHL_DriverModel.source
 · exact verify_observed
 · intro zero _ v sem _ _
   exact NHS_NewPort.slot base B std D sem v hash (Array.repeat 29#usize zero)
 · intro ctx _
   rfl
 · intro ctx a pending _ _ cells _
   rfl
#print axioms source
end AspisR1.NHW_DriverInstantiation
