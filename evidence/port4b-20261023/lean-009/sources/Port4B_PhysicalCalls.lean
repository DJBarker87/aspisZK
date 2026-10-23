import Port4B_Cuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_PhysicalCalls
open Aeneas Aeneas.Std Result VTop_Stages
open Port3_NativeBatchCalls (Indices Values)

/-- All roots and queries are the original physical fields. Scratch returned
by tree0 is passed to tree1, then its return is passed to tree2. -/
def Slots (leaves : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (proof : Slice U8)
    (p : verifier.Prepared) (folded : Array U8 32#usize) (batch : Usize) : Prop :=
  ∃ (idx1 idx2 idx3 : Indices) (val1 val2 val3 : Values),
    Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
      (VTop_Checkpoint.digest D) proof p.queries (Port3_BatchStage.root0 p) batch 0#usize
      (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize (Array.repeat 32#usize 0#u8)) hash =
      ok (.Ok (),idx1,val1) ∧
    Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
      (VTop_Checkpoint.digest D) proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx1 val1 hash =
      ok (.Ok (),idx2,val2) ∧
    Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
      (VTop_Checkpoint.digest D) proof p.queries folded batch 2#usize idx2 val2 hash =
      ok (.Ok (),idx3,val3)

variable {CoreError W : Type}

/-- Accepted installed TX1 itself supplies the three batch0 native returns.
This proves physical call binding, not P6 effects or parsed-root agreement. -/
theorem tx1_slots (base : Ops) (reserved : Bool) (leaves : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 (Port3_Parents.installed base reserved leaves geometry query finish)
      D semantic pub proof split hash none = ok (.Ok saved)) :
    ∃ p root, Slots leaves D hash proof p root 0#usize := by
  obtain ⟨p,root,batch⟩ := Port4B_Cuts.tx1_batch
    (Port3_Parents.installed base reserved leaves geometry query finish)
    D hash semantic pub proof split none saved accepted
  change Port3_BatchStage.batch leaves D proof p root 0#usize hash = ok (.Ok ()) at batch
  exact ⟨p,root,Port3_BatchStage.accepted_slot_calls leaves D proof p root 0#usize hash batch⟩

/-- Accepted installed TX2 supplies batch1 and the SAME resume Prepared;
there is no separately successful reader or freely chosen decoded state. -/
theorem tx2_slots (base : Ops) (reserved : Bool) (leaves : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (accepted : verifier.candidate.tx2_authenticated
      (Port3_Parents.installed base reserved leaves geometry query finish)
      D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ p a root,
      (Port3_Parents.installed base reserved leaves geometry query finish).op18
        D checkpoint proof pub .S2 hash = ok (.Ok (p,a)) ∧
      Slots leaves D hash proof p root 1#usize := by
  obtain ⟨p,a,root,resume,batch⟩ := Port4B_Cuts.tx2_batch
    (Port3_Parents.installed base reserved leaves geometry query finish)
    D hash pub proof checkpoint none accepted
  change Port3_BatchStage.batch leaves D proof p root 1#usize hash = ok (.Ok ()) at batch
  exact ⟨p,a,root,resume,Port3_BatchStage.accepted_slot_calls leaves D proof p root 1#usize hash batch⟩

#print axioms tx1_slots
#print axioms tx2_slots
end AspisR1.Port4B_PhysicalCalls
end
