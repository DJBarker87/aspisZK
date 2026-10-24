import Port5Q2_Provenance
import Port4A_CheckpointRows
import Port4A_PrefixReader

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_Checkpoint
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces CheckpointBytes5Effect CheckpointBytes5Inputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Port4C_QueryState (FK FE)
variable {CoreError W : Type}

def installed (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  Port4A_ReaderInstall.install
    (Port4C_Installed.installed base reserved batch geometry query finish) reserved

/-- ONE accepted TX1 and its SAME saved-byte reader call. All state provenance
is constructed from that TX1 prefix; only local observation/prepare/backend
ports and caller/ROM interpretation remain. Checkpoint8 is still the selector
reference, with the separately audited production native certificate domain. -/
theorem accepted (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (prepare : Port5Q2_Prepared.SessionAPrepare base)
    (basis : Port4C_BasisOuter.SessionABasis queryOps)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends queryOps)
    (lineCanonical : ∀ alpha values inverses value,
      queryOps.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {Hsh : Type} (D : aspis_core.digest.Digest32 Hsh) (hash : Hsh) (H : Bytes → State)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof pub : Slice U8) (stored publicBytes : Bytes) (split : Usize)
    (caller : CheckpointBytes5Join.S2S10CallerBinding (VTop_Checkpoint.digest D)
      hash H proof pub stored publicBytes)
    (saved : alloc.vec.Vec U8) (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (tx1 : verifier.candidate.tx1 (installed base reserved batch geometryOps queryOps finish)
      D semantic pub proof split hash none=ok (.Ok saved))
    (resumed : (installed base reserved batch geometryOps queryOps finish).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1))) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (fields : Port5Q2_Prepared.PreparedFields p) (size : a.weights.val.length=64)
      (canonical : CheckpointBytesBlocks.CanonicalFields
        (Port3_DecodeCoherence.inventory p a size fields.queries))
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry),
    VTop_Provenance.WriterPrefix (installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a ∧
    (installed base reserved batch geometryOps queryOps finish).op8 D p a proof pub hash=ok saved ∧
    Port5Q2_Ten.Inputs base (Port4C_Installed.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split p g geometry ∧
    ∀ m : OraclePortCheckpointStateC3.Prepared FK FE,
      Port5Q2_Advance.ObservationBinding (Port3_QueryStage.release queryOps)
        proof p g (Port3_QueryInstall.observer none) geometry m →
      ∃ after,
        run (VTop_Checkpoint.digest D) hash
          (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub) []=
          ok (.Ok (p1,a1),after) ∧
        CheckpointBytes4SavedFields.BodyMatches p1 a1
          (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
          (OraclePortCheckpointStateC3.write m).accumulator ∧
        observe after=CheckpointBytes5Join.six H stored publicBytes
          (OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body
            (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
            (OraclePortCheckpointStateC3.write m).accumulator (H stored) (H publicBytes)) := by
  obtain ⟨p,a,reached1,wrote⟩ := VTop_Provenance.writer_prefix _ D hash semantic pub proof split none saved tx1
  have reached2 := (Port4A_PrefixReader.prefix_iff
    (Port4C_Installed.installed base reserved batch geometryOps queryOps finish)
    reserved D hash semantic proof split p a).mp reached1
  obtain ⟨fields,size,canonical,g,geometry,cuts,provenance⟩ := Port5Q2_Provenance.reached base reserved batch
    geometryOps queryOps finish prepare basis arithmetic lineCanonical D hash semantic proof split p a reached2
  refine ⟨p,a,fields,size,canonical,g,geometry,reached1,wrote,cuts,?_⟩
  intro m binding
  obtain ⟨after,success,body,next,reservedEq,reads⟩ := Port4A_CheckpointRows.fields_and_reads base reserved
    D hash H p a proof pub stored publicBytes _ _ caller (provenance m binding)
    saved p1 a1 wrote resumed []
  refine ⟨after,success,body,?_⟩
  simpa only [observe,List.map_nil,List.nil_append] using reads

#print axioms accepted
end AspisR1.Port5Q2_Checkpoint
end
