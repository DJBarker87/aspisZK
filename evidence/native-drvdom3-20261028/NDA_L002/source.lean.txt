import NCU_DriverDomain
import SAP_OpeningCuts
import SAP_OpeningShape
import SAP_SemanticCanonical
import SAP_AlphaTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDA_DriverDomain
open Aeneas Aeneas.Std Result DrvC_Installation
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open NCT_DriverDomain (writerPrepared writerAccumulator)
variable {F C : Type}

/-- The installed preparation alone supplies S2, all 22 bounds, rho and
six prepared canonical groups. The same cut is used throughout. -/
theorem preparation (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :
    (writerPrepared cut.prepared).variant = .S2 ∧
    (∀ j : Fin 22, ((writerPrepared cut.prepared).queries.val[j.val]'(by
      simpa [(writerPrepared cut.prepared).queries.property] using j.isLt)).val < 262144) ∧
    OraclePortCkptAbi4Decode.CanonicalWide (writerPrepared cut.prepared).gamma ∧
    OraclePortCkptAbi4Decode.CanonicalWide (writerPrepared cut.prepared).kappa ∧
    (∀ j : Fin 2, OraclePortCkptAbi4Decode.CanonicalWide
      ((writerPrepared cut.prepared).alpha.val[j.val]'(by
        simpa [(writerPrepared cut.prepared).alpha.property] using j.isLt))) ∧
    OraclePortCkptAbi4Decode.Canonical (writerPrepared cut.prepared).rho ∧
    (∀ j : Fin 10, OraclePortCkptAbi4Decode.Canonical
      ((writerPrepared cut.prepared).semantic_alpha.val[j.val]'(by
        simpa [(writerPrepared cut.prepared).semantic_alpha.property] using j.isLt))) ∧
    OraclePortCkptAbi4Decode.CanonicalWide (writerPrepared cut.prepared).claim := by
  obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
    SAP_OpeningCuts.opening (current c) c.boundaries c.std (currentDigest c) () semantic proof
      cut.prepared (Array.repeat 29#usize cut.zero) cut.scratch cut.prepare
  have variant : (retainedView view).variant = AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant = _
    rw [sourceView_variant proof expanded y1 view wide]
    rfl
  have shape := SAP_OpeningShape.fields (retainedDigest (currentDigest c)) (retainedSem sem)
    (retainedView view) () out rs variant reached
  have semanticCanon := SAP_SemanticCanonical.alpha AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install c.std c.boundaries) (currentDigest c) semantic expanded () sem verify
  rw [←outEq]
  refine ⟨?_,shape.2.2.2.1,SAP_CanonicalCarrier.wide out.gamma canon.1,
    SAP_CanonicalCarrier.wide out.kappa canon.2,?_,shape.2.2.2.2,?_,
    SAP_CanonicalCarrier.wide out.claim claim⟩
  · change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant (currentVariant out.variant)) = _
    rw [shape.1]; rfl
  · intro j
    simpa only [writerPrepared,CheckpointBytes3Namespaces.toPrepared,
      CheckpointBytes3Namespaces.mapArray,List.getElem_map] using SAP_AlphaTransport.alpha out alpha j
  · have all : ∀ q ∈ out.semantic_alpha.val, SAP_CanonicalCarrier.CanonK q := by
      rw [shape.2.1]
      exact semanticCanon
    intro j
    simp only [writerPrepared,CheckpointBytes3Namespaces.toPrepared,Tx1Q_Carriers.prepared,
      currentPrepared,Tx1Q_Carriers.arr,AspisR1ClaimPreparedBridge.mapArray,
      CheckpointBytes3Namespaces.mapArray,List.getElem_map]
    apply SAP_CanonicalCarrier.qm
    exact all _ (List.getElem_mem _)

#print axioms preparation
end AspisR1.NDA_DriverDomain
end
