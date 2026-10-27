import RPz7_F3N_OriginalClaim
import RPz7_F3M_PreparedRemaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_PreparedClaim
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
attribute [local irreducible] decode
  JointFunctionalBinding.claimedValue

theorem claim {H : Type} (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : E) (out : AspisR1PublicPreparation.verifier.Prepared)
    (g : Array E 29#usize) (p : OraclePortCompactDraft.Parsed)
    (i : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144)
    (meaning : OriginalPayloadClaimMeaning sem y1 inactive (toClaimE out.gamma)
      (toClaimE out.kappa) (toClaimE out.claim) g)
    (six : F3L_PreparedModelSix.Fields out i q)
    (constant : i.data.c0=decode inactive)
    (selected : ∀ (point l : Usize) (hp : point.val<6) (hl : l.val<29)
      (scalar : AspisR1CurrentPreparedClaim.aspis_core.field.QM31),
      PublicSelectedSource sem y1 point l (fromClaimQ scalar) →
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed scalar=i.data.Y ⟨point.val,hp⟩ ⟨l.val,hl⟩) :
    (F3L_SourcePrepared.numeric out).claim=
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q).claim := by
  have source := F3N_OriginalClaim.value sem y1 inactive (toClaimE out.gamma)
    (toClaimE out.kappa) (toClaimE out.claim) g meaning i.data.Y selected
  have gamma : decode (toClaimE out.gamma)=i.data.gamma := six.1
  have kappa : decode (toClaimE out.kappa)=i.data.kappa := six.2.1
  rw [gamma,kappa,← constant] at source
  exact source

#print axioms claim
end AspisR1.F3N_PreparedClaim
end
