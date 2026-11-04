import Lean
import NFN_PhaseTransport
import NFS_NEV_RowStep
import Port3_NativeRowFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_RowLoop
open Aeneas Aeneas.Std Result ControlFlow NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Only control-flow/carrier transport is new. The imported push bridge and
its existing row arithmetic/phase induction are reused unchanged. -/
theorem association (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next : Usize)
    (basis : Array U32 256#usize) (fuel : Nat) (iter : NFS_NEV_RowStep.Iter)
    (b : NEV_AccumulateRaw.BatchedWeights) (width : v.val.length=64)
    (raw : b.raw.val.length=64) (finish : iter.end=64#usize)
    (span : iter.start.val+fuel=64) (global : next.val<22) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1
          iter v power next b 64#usize basis
        ok (toWeights out)) =
      verifier.accumulate_batched_with_node_loop1 (NBF_RowInstall.install ops)
        iter (mapVec toQ v) (toQ power) next (toWeights b) 64#usize basis := by
  induction fuel generalizing iter b with
  | zero =>
    have halt : iter.end.val≤ iter.start.val := by rw [finish];change 64≤ iter.start.val;omega
    obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
    subst o
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop1
      verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    simp [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
      verifier.accumulate_batched_with_node_loop1.body,run]
  | succ k ih =>
    have inside : iter.start.val<64 := by omega
    have mapped := NFS_NEV_RowStep.active ops v power next basis iter b width finish inside global
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop1
      verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    cases bodyRun : NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
        v power next 64#usize basis iter b with
    | fail error =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=fail error := by
        simpa only [bodyRun,bind_tc_fail] using mapped.symm
      simp only [modelRun,bind_tc_fail]
    | div =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=div := by
        simpa only [bodyRun,bind_tc_div] using mapped.symm
      simp only [modelRun,bind_tc_div]
    | ok flow =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=ok (NFS_NEV_RowStep.mapFlow flow) := by
        simpa only [bodyRun,bind_tc_ok] using mapped.symm
      obtain ⟨iter1,after,shape,counter,endpoint,length,terms⟩ :=
        Port3_NativeRowFrame.body_fields (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)
          (by rw [finish];exact inside)
          (by rw [finish];change 64≤b.raw.val.length;omega)
          (NFS_NEV_RowStep.mapFlow flow) modelRun
      cases flow with
      | done final => cases shape
      | cont pair =>
        rcases pair with ⟨cursor,result⟩
        have same : (cursor,toWeights result)=(iter1,after) := ControlFlow.cont.inj shape
        have cursors : cursor=iter1 := congrArg Prod.fst same
        have carriers : toWeights result=after := congrArg Prod.snd same
        rw [← cursors] at counter endpoint
        rw [← carriers] at length
        have size : result.raw.val.length=64 := by
          change result.raw.val.length=b.raw.val.length at length
          exact length.trans raw
        simp only [modelRun,NFS_NEV_RowStep.mapFlow,bind_tc_ok]
        exact ih cursor result size (endpoint.trans finish) (by omega)
#print axioms association
end NFS_NEV_RowLoop
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
