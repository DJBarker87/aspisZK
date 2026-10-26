import R1Z.PV_Src_FrozenInput

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FrozenPublic
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_FrozenInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem correspondence (i : Data (K := K))
    (success : @run external records (input i) = ok (.Ok (input i).compiled))
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords records (input i) = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (input i)))) := by
  rw [PV_Src_RecordReference.newRecords_eq] at hr
  have he := Result.ok.inj hr
  subst r
  have hs := @PV_Src_ReturnedSnapshot.returned_snapshot external records
    (input i).witness (outputValue (input i).request) (recipient (input i).request)
    (input i).change (forestPublic (input i).request) (input i).laneAnchor
    (input i).snapshot (input i).compiled success
  exact PV_Src_PublicParts.reference_parts PV_Src_CanonicalRoots.table (input i) hs
    (PV_Src_FrozenInput.frontier i) PV_Src_CanonicalRoots.meaning
    (fun l => PV_Src_CanonicalRoots.canonical l.castSucc)

#print axioms correspondence
end R1Z.PV_Src_FrozenPublic
