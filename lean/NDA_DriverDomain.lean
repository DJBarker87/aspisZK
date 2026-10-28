import NCU_DriverDomain
import SAP_OpeningCuts
import SAP_OpeningShape
import SAP_SemanticCanonical
import SAP_AlphaTransport
import NDA_QueryCanonical
import NDA_CircleCanonical
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

open CheckpointBytesBody CheckpointBytesBlocks CheckpointBytes5Writer

/-- The original writer inventory on the same Prepared/Accumulator. This is
only a value definition; it contains no new proposition or success premise. -/
def inventory (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :=
  fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed)
    (NCU_DriverDomain.control c semantic pub proof cut).1
    (preparation c semantic pub proof cut).2.1

/-- Exact before/after premise audit. Six of nine groups disappear by proof;
only the four coordinates, rhs and power remain, on the unchanged inventory. -/
theorem remaining_iff (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :
    NCT_DriverDomain.NonWeightCanonical (inventory c semantic pub proof cut) ↔
      (∀ j, OraclePortCkptAbi4Decode.Canonical ((inventory c semantic pub proof cut).coordinates j)) ∧
      OraclePortCkptAbi4Decode.CanonicalWide (inventory c semantic pub proof cut).rhs ∧
      OraclePortCkptAbi4Decode.Canonical (inventory c semantic pub proof cut).power := by
  rcases preparation c semantic pub proof cut with
    ⟨variant,qb,gamma,kappa,alpha,rho,semanticAlpha,claim⟩
  constructor
  · intro h; exact ⟨h.coordinates,h.rhs,h.power⟩
  · rintro ⟨coordinates,rhs,power⟩
    refine ⟨gamma,kappa,?_,rho,?_,coordinates,claim,rhs,power⟩
    · exact alpha
    · exact semanticAlpha

/-- Complete writer domain with only the exact residual field premises. -/
theorem domain (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (coordinates : ∀ j, OraclePortCkptAbi4Decode.Canonical ((inventory c semantic pub proof cut).coordinates j))
    (rhs : OraclePortCkptAbi4Decode.CanonicalWide (inventory c semantic pub proof cut).rhs)
    (power : OraclePortCkptAbi4Decode.Canonical (inventory c semantic pub proof cut).power) :
    KNE_Caller.WriterDomain (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) := by
  apply NCU_DriverDomain.domain c semantic pub proof cut (preparation c semantic pub proof cut).1
    (preparation c semantic pub proof cut).2.1
  exact (remaining_iff c semantic pub proof cut).mpr ⟨coordinates,rhs,power⟩

/-- The reduced premise is also exactly equivalent to the full writer domain
on this prefix; control/weight/shape/query facts are all already discharged. -/
theorem domain_iff (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :
    KNE_Caller.WriterDomain (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) ↔
      (∀ j, OraclePortCkptAbi4Decode.Canonical ((inventory c semantic pub proof cut).coordinates j)) ∧
      OraclePortCkptAbi4Decode.CanonicalWide (inventory c semantic pub proof cut).rhs ∧
      OraclePortCkptAbi4Decode.Canonical (inventory c semantic pub proof cut).power := by
  constructor
  · intro h
    exact ⟨h.canonical.coordinates,h.canonical.rhs,h.canonical.power⟩
  · rintro ⟨coordinates,rhs,power⟩
    exact domain c semantic pub proof cut coordinates rhs power

/-- Primitive laws suffice for every residual field. They are NOT proved for
arbitrary Configuration. No output domain is assumed in this composition. -/
theorem canonical_of_primitives (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (circle : NDA_CircleCanonical.Law c.boundaries)
    (query : NDA_QueryCanonical.Laws c.query) :
    NCT_DriverDomain.NonWeightCanonical (inventory c semantic pub proof cut) := by
  apply (remaining_iff c semantic pub proof cut).mpr
  have prep := preparation c semantic pub proof cut
  have coordinates := NDA_CircleCanonical.on_prefix c semantic pub proof cut circle
  have rho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared cut.prepared).rho :=
    prep.2.2.2.2.2.1
  have mutable := NDA_QueryCanonical.on_prefix c semantic pub proof cut query rho
  refine ⟨?_,mutable.1,mutable.2⟩
  intro j
  have hc := coordinates j
  fin_cases j <;>
    simpa only [inventory,fields,writerPrepared,CheckpointBytes3Namespaces.toPrepared,
      CheckpointBytes3Namespaces.mapArray,CheckpointBytes3Namespaces.toPoint,List.getElem_map]
      using hc

/-- All caller field gates follow from the two actual-primitive domains. -/
theorem domain_of_primitives (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8)
    (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (circle : NDA_CircleCanonical.Law c.boundaries)
    (query : NDA_QueryCanonical.Laws c.query) :
    KNE_Caller.WriterDomain (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) :=
  NCU_DriverDomain.domain c semantic pub proof cut (preparation c semantic pub proof cut).1
    (preparation c semantic pub proof cut).2.1
    (canonical_of_primitives c semantic pub proof cut circle query)

section Leaf
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytesDigest MultiproofConeCanonical
open KNE_Model KNE_Composition
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
/-- The original checkpoint leaf with S2, 22 bounds and six canonical groups
discharged. The ONLY residual caller fields are coordinates, rhs and power. -/
theorem leaf
(c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (coordinates : ∀ j, OraclePortCkptAbi4Decode.Canonical ((inventory c semantic pub proof cut).coordinates j))
    (rhs : OraclePortCkptAbi4Decode.CanonicalWide (inventory c semantic pub proof cut).rhs)
    (power : OraclePortCkptAbi4Decode.Canonical (inventory c semantic pub proof cut).power)

    (H : Bytes → State) (oracle : Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H)
    (native : Bytes → Bytes → Bytes → Prop)
    (valid : LocalCorrect native KND_Schedule.schedule)
    (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : Trace native (bodyEmissions (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain c semantic pub proof cut coordinates rhs power).size (domain c semantic pub proof cut coordinates rhs power).queriesBound)
      (stateOf hp) (stateOf hu)) [] (bytesOf body.val))
    (checksumWrite : native (bytesOf body.val) (bytesOf hc.val) (bytesOf out.val))
    (proofCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts proof) = ok hp)
    (publicCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts pub) = ok hu)
    (checksumCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (checksumParts body) = ok hc) :
    out.val.length = 1768 ∧
    out = LPm_CheckpointProgram.returned (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain c semantic pub proof cut coordinates rhs power).size (domain c semantic pub proof cut coordinates rhs power).queriesBound
      (domain c semantic pub proof cut coordinates rhs power).canonical (domain c semantic pub proof cut coordinates rhs power).next hp hu hc ∧
    run (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () (writer (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) proof pub) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts pub,hu)]) ++ [(checksumParts body,hc)]) ∧
    bytesOf out.val = OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf pub.val)
      (CheckpointBytesBlocks.prepared (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain c semantic pub proof cut coordinates rhs power).size (domain c semantic pub proof cut coordinates rhs power).queriesBound) (domain c semantic pub proof cut coordinates rhs power).canonical)
      (CheckpointBytesBlocks.accumulator (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain c semantic pub proof cut coordinates rhs power).size (domain c semantic pub proof cut coordinates rhs power).queriesBound) (domain c semantic pub proof cut coordinates rhs power).canonical) := by
  exact NCU_DriverDomain.leaf c semantic pub proof cut (preparation c semantic pub proof cut).1
    (preparation c semantic pub proof cut).2.1
    ((remaining_iff c semantic pub proof cut).mpr ⟨coordinates,rhs,power⟩)
    H oracle native valid hp hu hc body out before tr checksumWrite proofCall publicCall checksumCall
end Leaf
#print axioms leaf

section Leaf
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytesDigest MultiproofConeCanonical
open KNE_Model KNE_Composition
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
/-- Alternative export with no caller-output field assumptions. The actual
primitive laws remain explicit and must be instantiated; this is conditional. -/
theorem leaf_of_primitives
(c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (cut : NCU_DriverDomain.Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (circle : NDA_CircleCanonical.Law c.boundaries)
    (query : NDA_QueryCanonical.Laws c.query)

    (H : Bytes → State) (oracle : Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H)
    (native : Bytes → Bytes → Bytes → Prop)
    (valid : LocalCorrect native KND_Schedule.schedule)
    (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : Trace native (bodyEmissions (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain_of_primitives c semantic pub proof cut circle query).size (domain_of_primitives c semantic pub proof cut circle query).queriesBound)
      (stateOf hp) (stateOf hu)) [] (bytesOf body.val))
    (checksumWrite : native (bytesOf body.val) (bytesOf hc.val) (bytesOf out.val))
    (proofCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts proof) = ok hp)
    (publicCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts pub) = ok hu)
    (checksumCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (checksumParts body) = ok hc) :
    out.val.length = 1768 ∧
    out = LPm_CheckpointProgram.returned (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain_of_primitives c semantic pub proof cut circle query).size (domain_of_primitives c semantic pub proof cut circle query).queriesBound
      (domain_of_primitives c semantic pub proof cut circle query).canonical (domain_of_primitives c semantic pub proof cut circle query).next hp hu hc ∧
    run (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () (writer (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) proof pub) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts pub,hu)]) ++ [(checksumParts body,hc)]) ∧
    bytesOf out.val = OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf pub.val)
      (CheckpointBytesBlocks.prepared (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain_of_primitives c semantic pub proof cut circle query).size (domain_of_primitives c semantic pub proof cut circle query).queriesBound) (domain_of_primitives c semantic pub proof cut circle query).canonical)
      (CheckpointBytesBlocks.accumulator (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (domain_of_primitives c semantic pub proof cut circle query).size (domain_of_primitives c semantic pub proof cut circle query).queriesBound) (domain_of_primitives c semantic pub proof cut circle query).canonical) := by
  exact NCU_DriverDomain.leaf c semantic pub proof cut (preparation c semantic pub proof cut).1
    (preparation c semantic pub proof cut).2.1
    (canonical_of_primitives c semantic pub proof cut circle query)
    H oracle native valid hp hu hc body out before tr checksumWrite proofCall publicCall checksumCall
end Leaf
#print axioms leaf_of_primitives
#print axioms domain_iff

#print axioms domain_of_primitives
#print axioms remaining_iff
#print axioms domain
#print axioms canonical_of_primitives
#print axioms preparation
#print axioms query_distinct
end AspisR1.NDA_DriverDomain
end
