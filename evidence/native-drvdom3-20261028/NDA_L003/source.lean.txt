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

/-- The actual installed sampler returns 22 distinct coordinates, in their
original order. Bounds and injectivity come from its strict decoder. -/
theorem query_distinct (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :
    ∃ q : Fin 22 → Fin 262144,
      Function.Injective q ∧
      ∀ j : Fin 22, ((writerPrepared cut.prepared).queries.val[j.val]'(by
        simpa [(writerPrepared cut.prepared).queries.property] using j.isLt)).val = (q j).val := by
  obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
    SAP_OpeningCuts.opening (current c) c.boundaries c.std (currentDigest c) () semantic proof
      cut.prepared (Array.repeat 29#usize cut.zero) cut.scratch cut.prepare
  have variant : (retainedView view).variant = AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant = _
    rw [sourceView_variant proof expanded y1 view wide]
    rfl
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,first,serialized,second,third,unwrapped,extended1,extended2,fourth,query,last,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ (retainedDigest (currentDigest c)) (retainedSem sem)
      (retainedView view) () out rs variant reached
  have query' : AspisR1PublicPreparation.QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed)
      (retainedDigest (currentDigest c)) t4 31#u8 (retainedView view).final_message =
      ok (.Ok queries,t5) := query
  obtain ⟨q,decode,coordinates⟩ := F3K_SourceQueryDecode.source _ _ _ _ _ _ query'
  refine ⟨q,(LiteralQueryRead.decode_success _ q decode).2,?_⟩
  rw [←outEq,output]
  exact coordinates

#print axioms preparation
#print axioms query_distinct
end AspisR1.NDA_DriverDomain
end
