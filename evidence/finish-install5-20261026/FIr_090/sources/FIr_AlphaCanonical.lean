import FIq_TypedData
import FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_AlphaCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun
open AspisR1CurrentCaller.InstalledPreparation

theorem entry {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (e : RoundEvidence D pre) : FIp_SemanticValues.Canon e.q := by
  have h := SemanticCallSelectedCanonical.semantic_success_selected_canonical
    D e.beforeState.2.2 e.afterState.2.2 e.record e.q e.semanticOk
  exact h

theorem alpha {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (entries : List (RoundEvidence D pre)) (a : Array aspis_core.field.QM31 10#usize)
    (same : entries.map RoundEvidence.q=a.val) : ∀ q∈a.val,FIp_SemanticValues.Canon q := by
  rw [← same]
  intro q mem
  obtain ⟨e,member,rfl⟩ := List.mem_map.mp mem
  exact entry e

theorem verified {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify
      AspisS1ExtractedRoundChildren.children B D pub bytes hash=ok (.Ok sem)) :
    ∀ q∈(retainedSem sem).alpha.val,FIp_SemanticValues.Canon q := by
  obtain ⟨pre,before,after,running,record,decoded,initial,entries,parsed,rounds,
    read,decode,index,annotated,same,chain⟩ := FIq_SemanticSource.verified B D pub bytes hash sem success
  exact alpha entries (retainedSem sem).alpha same

#print axioms entry
#print axioms alpha
#print axioms verified
end AspisR1.FIr_AlphaCanonical
end
