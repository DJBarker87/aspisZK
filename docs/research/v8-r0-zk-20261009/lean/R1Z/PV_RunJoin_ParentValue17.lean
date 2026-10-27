import R1Z.PV_RunJoin_NodeValue17
import R1Z.PV_Src_PortParent
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ParentValue17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
local notation "M" => PV_RunJoin_FixtureRecords.M

/-- Transport a checked native copy-node value to the production parent. The
right and target bounds are explicit; no hash recurrence is reduced. -/
theorem source (left right target : Array U32 8#usize)
    (hr : Canon8 right) (ht : Canon8 target) (hcopy : node_digest_r left right = ok target) :
    pool_v1.format.pool_v1_tree_parent
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) left right = ok target := by
  obtain ⟨d,hd,hl,hc⟩ := nodeDigest_lift left right
    (digK (K := M) left) (digK (K := M) right) (fun _ => rfl) (fun _ => rfl) hr
  rw [PV_Src_Forest_DigestArguments.node_digest] at hcopy
  rw [hcopy] at hd
  have he : d = target := (Result.ok.inj hd).symm
  subst d
  rw [BuilderSemanticBridge.nodeDigest_eq (PV_RunJoin_FixtureRecords.base false)
    (toModel (PV_Src_Forest_PrimitiveArguments.wordWitness PV_RunJoin_ReferenceFixtureResults.transferWitness))] at hl
  apply PV_Src_PortParent.source
  · exact hr 7 (by decide)
  · exact ht
  · exact (funext hl).symm
#print axioms source
end R1Z.PV_RunJoin_ParentValue17
