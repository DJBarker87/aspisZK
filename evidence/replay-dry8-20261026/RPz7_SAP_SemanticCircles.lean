import RPz7_SAP_CircleCanonical
import RPz7_F3M_SemanticSource
import RPz7_PAln_CircleCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_SemanticCircles
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem coordinates (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify R
      (ClaimsUnrolledFinish.install std (F3M_CircleSource.install B)) D pub bytes hash=ok (.Ok sem)) :
    ∃ z0 z1,(retainedSem sem).z=Array.make 2#usize [z0,z1] ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  obtain ⟨pre,t0,t15,t25,cs,parsed,publicInit,trace,rows,qs,frames,
    r25,r26,z0,t26,z1,t27,read25,circle25,read26,circle26,tr,zEq⟩ :=
    F3M_SemanticSource.values R (ClaimsUnrolledFinish.install std (F3M_CircleSource.install B))
      D pub bytes hash sem success
  have row25 := (SourceFull25.validated_record_bytes pre 25#u8 r25 read25).1
  have row26 := (SourceFull25.validated_record_bytes pre 26#u8 r26 read26).1
  obtain ⟨block0,_,call0⟩ := PAln_CircleCalls.circle25_success _ (retainedDigest D)
    t25 t26 r25 z0 row25 circle25
  obtain ⟨block1,_,call1⟩ := PAln_CircleCalls.circle26_success _ (retainedDigest D)
    t26 t27 r26 z1 row26 circle26
  exact ⟨z0,z1,zEq,SAP_CircleCanonical.source block0 .First z0 call0,
    SAP_CircleCanonical.source block1 .Second z1 call1⟩

#print axioms coordinates
end AspisR1.SAP_SemanticCircles
end
