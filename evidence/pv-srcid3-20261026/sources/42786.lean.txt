import R1Z.PV_Src_PublicRootClosed
import R1Z.PV_Src_NativeIdentification
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PublicDeploymentAssociation
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

/-! Remaining installed-payload association. These are native P obligations,
not trust items. The same actual constructor result appears in returned_public.
No PubCorr or source-root equation is hidden in the interface. -/
structure Association {I : Type} (actualRecords : Records) (inputs : I → Input) : Prop where
  snapshot : ∀ i, (inputs i).compiled.public_statement.live_snapshot = (inputs i).snapshot
  frontier : ∀ i (l : Fin 20), Canon8 (inputs i).snapshot.frontier.val[l.val]!
  returned_public : ∀ i r, @newRecords actualRecords (inputs i) = ok r →
    PV_Src_Forest_PrimitiveArguments.wordPublic r.p =
      PV_Src_PublicHeader.publicRecord PV_Src_CanonicalRoots.table (inputs i)

theorem correspondence {K : Type} [Field K] [CharP K 2147483647]
    {I : Type} (actualRecords : Records) (inputs : I → Input)
    (association : Association actualRecords inputs) (i : I)
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords actualRecords (inputs i) = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i)))) := by
  rw [association.returned_public i r hr]
  exact PV_Src_PublicParts.reference_parts PV_Src_CanonicalRoots.table (inputs i)
    (association.snapshot i) (association.frontier i) PV_Src_CanonicalRoots.meaning
    (fun l => PV_Src_CanonicalRoots.canonical l.castSucc)

#print axioms correspondence
end R1Z.PV_Src_PublicDeploymentAssociation
