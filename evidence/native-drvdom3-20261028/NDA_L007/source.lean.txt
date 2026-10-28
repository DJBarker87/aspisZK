import NCU_DriverDomain
import SAP_OpeningCuts
import SAP_OpeningShape
import SAP_SemanticCircles
import SAP_CoordinateTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDA_CircleCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

/-- Missing primitive domain, on the actual retained circle slot. This does
not identify it with another installation or assume any driver's output. -/
def Law (B : FinishModel.Boundaries) : Prop :=
  ∀ block row point, B.circle block row = ok point →
    SAP_CanonicalCarrier.CanonK point.x ∧ SAP_CanonicalCarrier.CanonK point.y

/-- Existing emitted-wrapper arithmetic supplies this law if that is the
actual slot; no dictionary replacement is performed here. -/
theorem of_source (B : FinishModel.Boundaries) (same : B.circle = F3M_CircleSource.source) : Law B := by
  intro block row point call
  rw [same] at call
  exact SAP_CircleCanonical.source block row point call

/-- The two successful circle calls come from this very semantic verification. -/
theorem semantic (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (law : Law B)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify R
      (ClaimsUnrolledFinish.install std B) D pub bytes hash = ok (.Ok sem)) :
    ∃ z0 z1, (retainedSem sem).z = Array.make 2#usize [z0,z1] ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  obtain ⟨pre,t0,t15,t25,cs,parsed,publicInit,trace,rows,qs,frames,
    r25,r26,z0,t26,z1,t27,read25,circle25,read26,circle26,tr,zEq⟩ :=
    F3M_SemanticSource.values R (ClaimsUnrolledFinish.install std B)
      D pub bytes hash sem success
  have row25 := (SourceFull25.validated_record_bytes pre 25#u8 r25 read25).1
  have row26 := (SourceFull25.validated_record_bytes pre 26#u8 r26 read26).1
  obtain ⟨block0,_,call0⟩ := PAln_CircleCalls.circle25_success _ (retainedDigest D)
    t25 t26 r25 z0 row25 circle25
  obtain ⟨block1,_,call1⟩ := PAln_CircleCalls.circle26_success _ (retainedDigest D)
    t26 t27 r26 z1 row26 circle26
  exact ⟨z0,z1,zEq,law block0 .First z0 call0,law block1 .Second z1 call1⟩

/-- Coordinates of this currentInstalled prefix, under only its primitive law. -/
theorem on_prefix {F C : Type} (c : DrvC_Installation.Configuration F C)
    (pubSemantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (DrvC_Installation.currentInstalled c)
      (DrvC_Installation.currentDigest c) pubSemantic pub proof ()) (law : Law c.boundaries) :
    ∀ j : Fin 4, OraclePortCkptAbi4Decode.Canonical
      (CheckpointBytes3Namespaces.toK (match j.val with
        | 0 => ((Tx1Q_Carriers.prepared cut.prepared).z.val[0]'(by
            simp [(Tx1Q_Carriers.prepared cut.prepared).z.property])).x
        | 1 => ((Tx1Q_Carriers.prepared cut.prepared).z.val[0]'(by
            simp [(Tx1Q_Carriers.prepared cut.prepared).z.property])).y
        | 2 => ((Tx1Q_Carriers.prepared cut.prepared).z.val[1]'(by
            simp [(Tx1Q_Carriers.prepared cut.prepared).z.property])).x
        | _ => ((Tx1Q_Carriers.prepared cut.prepared).z.val[1]'(by
            simp [(Tx1Q_Carriers.prepared cut.prepared).z.property])).y)) := by
  open DrvC_Installation in
    obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
      SAP_OpeningCuts.opening (current c) c.boundaries c.std (currentDigest c) () pubSemantic proof
        cut.prepared (Array.repeat 29#usize cut.zero) cut.scratch cut.prepare
  have variant : (retainedView view).variant = transport.Variant.S2 := by
    change retainedVariant view.variant = _
    rw [AspisR1CurrentCaller.InstalledPreparation.sourceView_variant proof expanded y1 view wide]
    rfl
  have shape := SAP_OpeningShape.fields (retainedDigest (DrvC_Installation.currentDigest c))
    (retainedSem sem) (retainedView view) () out rs variant reached
  obtain ⟨z0,z1,z,c0,c1⟩ := semantic AspisS1ExtractedRoundChildren.children c.boundaries c.std law
    (DrvC_Installation.currentDigest c) pubSemantic expanded () sem verify
  rw [←outEq]
  exact SAP_CoordinateTransport.coordinates out z0 z1 (shape.2.2.1.trans z) c0 c1

#print axioms of_source
#print axioms semantic
#print axioms on_prefix
end AspisR1.NDA_CircleCanonical
end
