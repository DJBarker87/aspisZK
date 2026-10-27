import R1Z.PV_RunJoin_OutputChecks16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeValue17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem source (left right target : Array U32 8#usize)
    (hr : Canon8 right) (ht : Canon8 target)
    (hm : R0P.nodeCompress (digK (K := M) left) (digK (K := M) right) = digK (K := M) target) :
    node_digest_r left right = ok target := by
  obtain ⟨d,hd,hl,hc⟩ := nodeDigest_lift left right
    (digK (K := M) left) (digK (K := M) right) (fun _ => rfl) (fun _ => rfl) hr
  rw [BuilderSemanticBridge.nodeDigest_eq (PV_RunJoin_FixtureRecords.base false)
    (toModel (PV_Src_Forest_PrimitiveArguments.wordWitness PV_RunJoin_ReferenceFixtureResults.transferWitness)),hm] at hl
  rw [PV_Src_Forest_DigestArguments.node_digest]
  exact hd.trans (congrArg Result.ok (PV_RunJoin_TreeValue16.unique d target hc ht hl))
#print axioms source
end R1Z.PV_RunJoin_NodeValue17
