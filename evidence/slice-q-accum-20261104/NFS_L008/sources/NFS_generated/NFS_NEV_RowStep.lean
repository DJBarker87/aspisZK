import Lean
import NFN_PhaseTransport
import NFS_NEV_PushUse
import NFS_NEV_BorrowMaps
import NFS_NEV_CtorResults
import NBF_BasisInstall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_RowStep
open Aeneas Aeneas.Std Result ControlFlow NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Iter := core.ops.range.Range Usize
abbrev RawFlow := ControlFlow (Iter × NEV_AccumulateRaw.BatchedWeights) NEV_AccumulateRaw.BatchedWeights
abbrev Flow := ControlFlow (Iter × AspisR1Stage2.verifier.BatchedWeights) AspisR1Stage2.verifier.BatchedWeights

def mapFlow : RawFlow → Flow
 | .cont (iter,b) => .cont (iter,toWeights b)
 | .done b => .done (toWeights b)

/-- One actual row iteration, preserving complete Result and returned BW.
Diagnostic conversions execute in the source, are total on all raw words,
and feed the deployed no-op trace; no diagnostic value is an observable. -/
theorem active (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next : Usize)
    (basis : Array U32 256#usize) (iter : Iter) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : v.val.length=64) (finish : iter.end=64#usize)
    (inside : iter.start.val<64) (global : next.val<22) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
          v power next 64#usize basis iter b
        ok (mapFlow out)) =
      verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
        (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b) := by
  obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter (by rw [finish];exact inside))
  subst o
  obtain ⟨word,basisRead,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec basis iter.start (by change iter.start.val<basis.val.length;rw [basis.property];change iter.start.val<256;omega))
  obtain ⟨q,read,mappedRead⟩ := NFS_NEV_BorrowMaps.weight_read ops v iter.start (by omega)
  have mappedRead' : core.slice.index.Slice.index
      (core.slice.index.SliceIndexUsizeSlice NBF_RowInstall.Q)
      (mapVec toQ v).deref iter.start=ok (toQ q) := mappedRead
  have multiplication := NBF_BasisInstall.checked_mul next 64#usize
    (by change next.val*64≤4096;omega)
  have productValue := Port3_Wrapping.wrap_mul_value next 64#usize
    (by change next.val*64≤4096;omega)
  have offset := Port3_Wrapping.checked_add (Usize.wrapping_mul next 64#usize) iter.start
    (by rw [productValue];change next.val*64+iter.start.val≤4096;omega)
  have use := NFS_NEV_PushUse.association b iter.start power word
  have lifted := congrArg (fun result : Result AspisR1Stage2.verifier.BatchedWeights =>
    do let out ← result;ok (cont (iter1,out) : Flow)) use
  simpa [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
    verifier.accumulate_batched_with_node_loop1.body,NBF_RowInstall.install,
    run,NEV_AccumulateRaw.basis_at,basisRead,read,mappedRead',
    multiplication,offset,lift,NFS_NEV_CtorResults.qm,NFS_NEV_CtorResults.m31,
    NEV_AccumulateRaw.trace.value,bind_assoc_eq,mapFlow] using lifted

theorem stop (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next width : Usize)
    (basis : Array U32 256#usize) (iter : Iter) (b : NEV_AccumulateRaw.BatchedWeights)
    (halt : iter.end.val≤ iter.start.val) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
          v power next width basis iter b
        ok (mapFlow out)) =
      verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
        (mapVec toQ v) (toQ power) next width basis iter (toWeights b) := by
  obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
  subst o
  simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
    verifier.accumulate_batched_with_node_loop1.body,run,bind_tc_ok]
  rfl
#print axioms active
#print axioms stop
end NFS_NEV_RowStep
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
