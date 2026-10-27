import RPz7_F3L_WriterBody
import CheckpointBytes5Join
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_CheckpointNumeric
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join
open CheckpointBytes4SavedFields
open F3K_CheckpointPreparedFields CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The complete six source reads are on the numeric source body. Identifying
that numeric body with F3's discovered model remains a separate obligation. -/
theorem stage {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (reserved : Bool)
    (out : AspisR1PublicPreparation.verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (stored physical : Bytes)
    (caller : S2S10CallerBinding D hash H proof pub stored physical)
    (variant : out.variant=.S2) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10) (p2 : verifier.Prepared) (a2 : verifier.Accumulator) (after : Log)
    (success : run D hash (CheckpointBytes5Join.stage reserved (writerPrepared out) (toAccumulator a) proof pub)
      []=ok (.Ok (p2,a2),after)) :
    BodyMatches p2 a2 (F3L_SourcePrepared.numeric out) (CheckpointBytes5Output.accumulator a) ∧
    observe after=six H stored physical (OraclePortPhysicalFrameDraft.domain++
      OraclePortCheckpointAbiC5.body (F3L_SourcePrepared.numeric out) (CheckpointBytes5Output.accumulator a)
        (H stored) (H physical)) := by
  have provenance : S1S7S8StateProvenance (writerPrepared out) (toAccumulator a)
      (F3L_SourcePrepared.numeric out) (CheckpointBytes5Output.accumulator a) := by
    refine ⟨?_,by simpa only [toAccumulator,mapVec,List.length_map] using size,qb,canonical,next,?_,?_⟩
    · change toVariant (Tx1Q_Carriers.variant (AspisR1CurrentCaller.InstalledPreparation.currentVariant out.variant))=.S2
      rw [variant]
      rfl
    · exact F3L_WriterPreparedEq.numeric out _ _ qb canonical
    · exact F3L_WriterAccumulator.numeric _ a size qb canonical next
  have checked := successful_fields_and_reads D hash H reserved (writerPrepared out) (toAccumulator a)
    proof pub stored physical _ _ caller provenance p2 a2 [] after success
  exact ⟨checked.1,by simpa only [observe,List.map_nil,List.nil_append] using checked.2.2.2⟩

#print axioms stage
end AspisR1.F3L_CheckpointNumeric
end
