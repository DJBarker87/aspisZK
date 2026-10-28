import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op82Source
import R1Z.PV_CB_Op83Source
import R1Z.PV_CB_Op84Source
import R1Z.PV_CB_Op86Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Merkle
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op82_source (ops : ExternalFuns) :
    (selected ops).op82 = .ok PV_CB_ShippedOp82.aspis_core.r0.merkle.C1_TAG := by
  exact PV_CB_Op82Source.op82_source ops
#print axioms op82_source
theorem op83_source (ops : ExternalFuns) :
    (selected ops).op83 = .ok PV_CB_ShippedOp83.aspis_core.r0.merkle.C2_TAG := by
  exact PV_CB_Op83Source.op83_source ops
#print axioms op83_source
theorem op84_source (ops : ExternalFuns)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (tag : U8) (values : Slice U8) :
    (selected ops).op84 hash tag values =
      PV_CB_ShippedOp84.aspis_core.r0.merkle.leaf_with_digest
        PV_CB_ShippedOp84.aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash tag values := by
  exact PV_CB_Op84Source.op84_source ops hash tag values
#print axioms op84_source
theorem op86_source (ops : ExternalFuns) :
    (selected ops).op86 = .ok PV_CB_ShippedOp86.aspis_core.r0.opening.LANES := by
  exact PV_CB_Op86Source.op86_source ops
#print axioms op86_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Merkle
