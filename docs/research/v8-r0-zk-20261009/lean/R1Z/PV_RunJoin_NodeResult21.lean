import R1Z.PV_RunJoin_NodeValue17
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeResult21
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.poseidonPermutation R0P.nodeCompress
/-- Extract the symbolic field law from an already proved successful source call. -/
theorem field (left right target : Array U32 8#usize) (hr : Canon8 right)
    (h : node_digest_r left right = ok target) :
    R0P.nodeCompress (digK (K := M) left) (digK (K := M) right) = digK target := by
  obtain ⟨d,hd,hl,_⟩ := nodeDigest_lift left right
    (digK (K := M) left) (digK (K := M) right) (fun _ => rfl) (fun _ => rfl) hr
  rw [BuilderSemanticBridge.nodeDigest_eq (PV_RunJoin_FixtureRecords.base false)
    (toModel (PV_Src_Forest_PrimitiveArguments.wordWitness PV_RunJoin_ReferenceFixtureResults.transferWitness))] at hl
  rw [PV_Src_Forest_DigestArguments.node_digest] at h
  have he : d = target := Result.ok.inj (hd.symm.trans h)
  subst d
  funext i
  exact (hl i).symm
#print axioms field
end R1Z.PV_RunJoin_NodeResult21
