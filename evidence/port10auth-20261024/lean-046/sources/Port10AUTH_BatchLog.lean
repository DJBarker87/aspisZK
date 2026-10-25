import Port10AUTH_Tree
import Port9OR_Batch

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_BatchLog
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)

theorem bind_success {A B X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (p : Code A) (k : A → Code B) (a : A) (success : erase D hash p=ok a) :
    Port9OR_Code.trace D hash (p >>= k)=
      ((Port9OR_Code.trace D hash p).1++(Port9OR_Code.trace D hash (k a)).1,
        (Port9OR_Code.trace D hash (k a)).2) := by
  rw [Port10AUTH_Trace.trace_bind]
  have value := (Port9OR_Code.trace_value D hash p).trans success
  cases h : Port9OR_Code.trace D hash p with
  | mk log result => rw [h] at value;dsimp only at value;rw [value]

/-- Actual three accepted source trees, exact roots and successive scratch
returns determine the full batch observation in chronological slot order. -/
theorem logs (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X) (proof : Slice U8) (p : verifier.Prepared)
    (folded : Digest) (batch : Usize)
    (idx1 idx2 idx3 : Indices) (val1 val2 val3 : Values)
    (c0 : erase D hash (Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root0 p) batch 0#usize
      Port4B_BatchJoin.initial.idx Port4B_BatchJoin.initial.val)=ok (.Ok (),idx1,val1))
    (c1 : erase D hash (Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root1 p) batch 1#usize
      idx1 val1)=ok (.Ok (),idx2,val2))
    (c2 : erase D hash (Port9OR_BatchTree.code base D hash proof p.queries folded batch 2#usize
      idx2 val2)=ok (.Ok (),idx3,val3)) :
    (Port9OR_Code.trace D hash (Port9OR_Batch.code base D hash proof p folded batch)).1=
      (Port9OR_Code.trace D hash (Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root0 p) batch 0#usize
        Port4B_BatchJoin.initial.idx Port4B_BatchJoin.initial.val)).1 ++
      (Port9OR_Code.trace D hash (Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root1 p) batch 1#usize
        idx1 val1)).1 ++
      (Port9OR_Code.trace D hash (Port9OR_BatchTree.code base D hash proof p.queries folded batch 2#usize idx2 val2)).1 := by
  have h0 : Array.index_usize p.roots 0#usize=ok (Port3_BatchStage.root0 p) := by
    simp [Array.index_usize,Port3_BatchStage.root0]
  have h1 : Array.index_usize p.roots 1#usize=ok (Port3_BatchStage.root1 p) := by
    simp [Array.index_usize,Port3_BatchStage.root1]
  unfold Port9OR_Batch.code
  rw [Port10AUTH_Leaf.lift_bind,h0]
  change (Port9OR_Code.trace D hash (do
    let r1 ← liftResult (Array.index_usize p.roots 1#usize)
    Port9OR_Batch.values base D hash proof p.queries
      (Array.make 3#usize [Port3_BatchStage.root0 p,r1,folded]) batch)).1=_
  rw [Port10AUTH_Leaf.lift_bind,h1]
  change (Port9OR_Code.trace D hash (Port9OR_Batch.values base D hash proof p.queries
    (Array.make 3#usize [Port3_BatchStage.root0 p,Port3_BatchStage.root1 p,folded]) batch)).1=_
  unfold Port9OR_Batch.values
  simp only [Port10AUTH_Leaf.lift_bind,Array.index_usize,Array.make,Array.getElem?_Usize_eq,List.getElem?_cons_zero,
    List.getElem?_cons_succ,show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
    show (2#usize).val=2 from rfl]
  rw [bind_success D hash _ _ _ c0]
  change (Port9OR_Code.trace D hash (Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root0 p) batch 0#usize
    Port4B_BatchJoin.initial.idx Port4B_BatchJoin.initial.val)).1 ++
    (Port9OR_Code.trace D hash (do
      let (r,idx,val) ← Port9OR_BatchTree.code base D hash proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx1 val1
      let cf ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r)
      match cf with
      | .Continue _ => do
        let (r,_,_) ← Port9OR_BatchTree.code base D hash proof p.queries folded batch 2#usize idx val
        let cf ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r)
        match cf with
        | .Continue _ => pure (core.result.Result.Ok ())
        | .Break e => liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) e)
      | .Break e => liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) e))).1=_
  rw [bind_success D hash _ _ _ c1]
  simp only [Port10AUTH_Leaf.lift_bind,core.result.Result.Insts.CoreOpsTry.branch]
  rw [bind_success D hash _ _ _ c2]
  simp only [Port10AUTH_Leaf.lift_bind,core.result.Result.Insts.CoreOpsTry.branch,Port10AUTH_Leaf.pure_trace,
    List.append_nil,List.append_assoc]

#print axioms bind_success
#print axioms logs
end AspisR1.Port10AUTH_BatchLog
end
