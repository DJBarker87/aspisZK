import Port6CK_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Ordered
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces CheckpointBytes5Effect CheckpointBytes5Inputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Port6CK_Semantic (Unwrap)

def stage (reserved : Bool) (unwrap : Unwrap)
    (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (proof pub : Slice U8) : Code (core.result.Result (verifier.Prepared × verifier.Accumulator) AspisR1Stage2.verifier.Error) := do
  let ck ← CheckpointBytes5Writer.writer p a proof pub
  CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2

theorem combined_run (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8) (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (wrote : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved)
    (resumed : Port6CK_Reader.reader reserved unwrap D (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1)))
    (before : Log) :
    ∃ after,
      run (VTop_Checkpoint.digest D) hash (stage reserved unwrap (toPrepared p) (toAccumulator a) proof pub) before=ok (.Ok (p1,a1),after) ∧
      run (VTop_Checkpoint.digest D) hash (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub) before=ok (.Ok (p1,a1),after) := by
  obtain ⟨middle,writerRun⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved wrote before
  obtain ⟨after,current,retained⟩ := Port6CK_Reader.runs reserved unwrap unwrap_ok D hash
    (VTop_Checkpoint.checkpointSlice saved) proof pub p1 a1 middle resumed
  refine ⟨after,?_,?_⟩
  · simp only [stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
    exact current
  · simp only [CheckpointBytes5Join.stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
    exact retained

variable {CoreError W : Type}
/-- The six-read theorem on the CURRENT reader program, with the SAME
checkpoint and returned pair. The reader log is transported without reordering. -/
theorem accepted (base : Ops) (reserved : Bool) (panic : Port6CK_Checkpoint.Panic)
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
    (tx1 : verifier.candidate.tx1 (Port6CK_Checkpoint.installed base reserved panic batch geometryOps queryOps finish)
      D semantic pub proof split hash none=ok (.Ok saved))
    (resumed : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps queryOps finish).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1))) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (fields : Port5Q2_Prepared.PreparedFields p) (size : a.weights.val.length=64)
      (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size fields.queries)),
      VTop_Provenance.WriterPrefix (Port6CK_Checkpoint.installed base reserved panic batch geometryOps queryOps finish)
        D hash semantic proof split none p a ∧
      (Port6CK_Checkpoint.installed base reserved panic batch geometryOps queryOps finish).op8 D p a proof pub hash=ok saved ∧
      p1=p ∧ a1=a ∧ a.next.val=10 ∧ split.val=10 ∧
      ∃ after,
        run (VTop_Checkpoint.digest D) hash
          (stage reserved (Port6CK_Checkpoint.unwrap panic) (toPrepared p) (toAccumulator a) proof pub) []=
          ok (.Ok (p1,a1),after) ∧
        observe after=CheckpointBytes5Join.six H stored publicBytes
          (OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body
            (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
            (CheckpointBytesBlocks.accumulator (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
            (H stored) (H publicBytes)) := by
  obtain ⟨p,a,fields,size,canonical,reached1,wrote,sameP,sameA,next,splitEq,after,retained,reads⟩ :=
    Port6CK_Checkpoint.accepted base reserved panic batch geometryOps queryOps finish
      prepare basis arithmetic lineCanonical D hash H semantic proof pub stored publicBytes split
      caller saved p1 a1 tx1 resumed
  obtain ⟨after1,current,retained1⟩ := combined_run reserved (Port6CK_Checkpoint.unwrap panic)
    (fun _ _ => rfl) D hash p a proof pub saved p1 a1 wrote resumed []
  have logs : after1=after := congrArg Prod.snd (Result.ok.inj (retained1.symm.trans retained))
  subst after1
  exact ⟨p,a,fields,size,canonical,reached1,wrote,sameP,sameA,next,splitEq,after,current,reads⟩

#print axioms combined_run
#print axioms accepted
end AspisR1.Port6CK_Ordered
end
