import NJG_CurrentEquation
import NHW_Prepare
import NHW_DriverInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_CallerInstall
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- Install the complete SAME-value SOURCE/MODEL op9 equation in NHW/NHL.
The chosen ops is explicitly a packet interpretation, not the native base ops;
no direct-native prepare/tx1 or writer row is promoted by this theorem. -/
theorem prepare (base : Ops) (reserved : Bool)
 (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (g : NHL_PrepareStages.Scratch) :
 NHL_EmittedPrepare.prepare
  (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
  D pubdata proof hash none g=
 verifier.candidate.prepare
  (NHL_PrepareModel.children
   (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
   (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))
  D pubdata proof hash none g := by
 apply NHW_Prepare.source
 intro v _reached
 exact NJG_CurrentEquation.slot base seed std D pubdata v.semantic hash

theorem tx1 (base : Ops) (reserved : Bool)
 (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) :
 NHW_EmittedTx1.tx1
  (NHL_Packets.installed
   (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
    (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved)
  (NHW_EmittedPrepare.prepare
   (NHL_Packets.installed
    (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
     (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved))
  D pubdata publicBytes proof k hash none=
 verifier.candidate.tx1
  (NHL_DriverModel.txOps
   (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
    (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))
   (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std) reserved)
  D pubdata publicBytes proof k hash none := by
 apply NHW_DriverInstantiation.source
 intro v _reached
 exact NJG_CurrentEquation.slot base seed std D pubdata v.semantic hash

#print axioms prepare
#print axioms tx1
end AspisR1.NJG_CallerInstall
end
