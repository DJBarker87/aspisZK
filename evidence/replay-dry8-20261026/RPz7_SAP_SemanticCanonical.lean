import RPz7_SAP_SampleCanonical
import RPz7_F3M_SemanticSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_SemanticCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem alpha (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify R B D pub bytes hash=ok (.Ok sem)) :
    ∀ q ∈ (retainedSem sem).alpha.val,SAP_CanonicalCarrier.CanonK q := by
  obtain ⟨pre,t0,t15,t25,cs,parsed,publicInit,trace,rows,qs,frames,circles⟩ :=
    F3M_SemanticSource.values R B D pub bytes hash sem success
  intro q member
  apply SAP_SampleCanonical.calls cs q
  rw [qs]
  exact List.mem_append_right _ member

#print axioms alpha
end AspisR1.SAP_SemanticCanonical
end
