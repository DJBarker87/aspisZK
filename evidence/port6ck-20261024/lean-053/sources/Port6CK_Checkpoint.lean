import Port6CK_Prefix
import Port6CK_BodySelf
import Port4A_CheckpointRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Checkpoint
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces CheckpointBytes5Effect CheckpointBytes5Inputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Port6CK_Semantic (Unwrap)
variable {CoreError W : Type}

abbrev Panic := (N : Usize) → core.array.TryFromSliceError → Result (Array U8 N)
def unwrap (panic : Panic) : Unwrap := fun N => OraclePortCkptAbi2Unwrap.unwrapWithPanic (panic N)

def installed (base : Ops) (reserved : Bool) (panic : Panic)
    (batch : Port3_NativeBatchBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  Port6CK_Reader.install (Port4C_Installed.installed base reserved batch geometry query finish)
    reserved (unwrap panic)

/-- ONE actual TX1, its saved Vec, and CURRENT native-helper op18 return.
Canonical physical provenance is constructed from that prefix. No model
advance, cross-TX accumulator agreement or independent reader success is a
premise. Every Prepared/accumulator field and the next counter are recovered. -/
theorem accepted (base : Ops) (reserved : Bool) (panic : Panic)
    (batch : Port3_NativeBatchBody.Ops)
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
    (tx1 : verifier.candidate.tx1 (installed base reserved panic batch geometryOps queryOps finish)
      D semantic pub proof split hash none=ok (.Ok saved))
    (resumed : (installed base reserved panic batch geometryOps queryOps finish).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1))) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (fields : Port5Q2_Prepared.PreparedFields p) (size : a.weights.val.length=64)
      (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size fields.queries)),
      VTop_Provenance.WriterPrefix (installed base reserved panic batch geometryOps queryOps finish)
        D hash semantic proof split none p a ∧
      (installed base reserved panic batch geometryOps queryOps finish).op8 D p a proof pub hash=ok saved ∧
      p1=p ∧ a1=a ∧ a.next.val=10 ∧ split.val=10 ∧
      ∃ after,
        run (VTop_Checkpoint.digest D) hash
          (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub) []=
          ok (.Ok (p1,a1),after) ∧
        observe after=CheckpointBytes5Join.six H stored publicBytes
          (OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body
            (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
            (CheckpointBytesBlocks.accumulator (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
            (H stored) (H publicBytes)) := by
  obtain ⟨p,a,prefix,wrote⟩ := VTop_Provenance.writer_prefix _ D hash semantic pub proof split none saved tx1
  have reached := (Port6CK_Prefix.same
    (Port4C_Installed.installed base reserved batch geometryOps queryOps finish) reserved
    (unwrap panic) D hash semantic proof split p a).mp prefix
  obtain ⟨fields,reservedEq,splitEq,next,size,canonical⟩ := Port5Q2_Prepared.reached base reserved batch geometryOps queryOps finish
    prepare basis arithmetic lineCanonical D hash semantic proof split p a reached
  have provenance : CheckpointBytes5Join.S1S7S8StateProvenance (toPrepared p) (toAccumulator a)
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
      (CheckpointBytesBlocks.accumulator (Port3_DecodeCoherence.inventory p a size fields.queries) canonical) := by
    refine ⟨?_,?_,fields.queries,canonical,next,rfl,rfl⟩
    · change toVariant p.variant=_
      rw [fields.variant]
      rfl
    · simpa only [toAccumulator,mapVec,List.length_map] using size
  have retained := Port6CK_Reader.accepted reserved (unwrap panic) (fun _ _ => rfl)
    D hash (VTop_Checkpoint.checkpointSlice saved) proof pub p1 a1 resumed
  obtain ⟨after,called,body,next1,_,reads⟩ := Port4A_CheckpointRows.fields_and_reads base reserved
    D hash H p a proof pub stored publicBytes _ _ caller provenance saved p1 a1 wrote retained []
  have self := Port6CK_BodySelf.fields p a fields.variant size fields.queries canonical
  have same := Port6CK_BodyUnique.unique p p1 a a1 _ _ self body (next.trans next1.symm)
  refine ⟨p,a,fields,size,canonical,prefix,wrote,same.1.symm,same.2.symm,next,splitEq,after,called,?_⟩
  simpa only [observe,List.map_nil,List.nil_append] using reads

#print axioms accepted
end AspisR1.Port6CK_Checkpoint
end
