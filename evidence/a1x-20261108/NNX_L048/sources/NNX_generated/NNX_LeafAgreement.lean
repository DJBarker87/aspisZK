import NNX_LeafShape
import NNV_CheckpointDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_LeafAgreement
open Aeneas Aeneas.Std Result NNH_Run5bCtx
open AspisV8R19.SqueezeOracleBridge
/-- The precise reached leaf domain, not unrestricted short openings. -/
theorem source {W Tx : Type} (c : Ctx W Tx) (kind : Usize) (opening : Slice U8)
 (length : opening.val.length=832) :
 (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)).digest ()
  (Port4B_LeafCode.input kind opening) =
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBC_CohortHash.H (envOf c))
  (Port4B_LeafCode.input kind opening)) := by
 rw [NNV_CheckpointDigest.source]
 unfold MultiproofConePhysicalTransport.rawOracle
 rw [LIBC_CohortHash.output (envOf c) _ (NNX_LeafShape.source kind opening length)]
 rfl
#print axioms source
end AspisR1.NNX_LeafAgreement
end
