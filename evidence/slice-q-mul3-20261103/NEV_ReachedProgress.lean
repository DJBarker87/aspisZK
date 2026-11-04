import NEV_RowStep
import NEV_PushDomains
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_ReachedProgress
open Aeneas Aeneas.Std Result ControlFlow NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- The existing phase induction transfers to the SAME actual successful
iteration. Thus a caller need not assume a fresh row bound at each call. -/
theorem next (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (global : Usize)
    (basis : Array U32 256#usize) (iter cursor : NEV_RowStep.Iter)
    (b after : NEV_AccumulateRaw.BatchedWeights) (t : Nat)
    (width : v.val.length=64) (finish : iter.end=64#usize)
    (inside : iter.start.val<64) (globalBound : global.val<22)
    (progress : S7JoinRowsTrace.Progress t iter.start.val (Port3_RowsInstall.toBW (toWeights b)))
    (canonical : NBF_PowerStep.Canonical (toQ power))
    (basisCanonical : ∀ j : Usize,j.val<64 → ∀ m,Array.index_usize basis j=ok m → m.val<2^31-1)
    (run : NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
      v power global 64#usize basis iter b=ok (cont (cursor,after))) :
    cursor.start.val=iter.start.val+1 ∧ cursor.end=iter.end ∧
      S7JoinRowsTrace.Progress t cursor.start.val (Port3_RowsInstall.toBW (toWeights after)) := by
  have limbs : ∀ k,(S7Kani2OwnedRowRefinement.powerLimb
      (Port3_RowsInstall.toK (toQ power)) k).val<2^31-1 := by
    intro k
    exact canonical k
  obtain ⟨iter1,b1,step,start,endpoint,successor⟩ := NBF_Progress.body ops
    (mapVec toQ v) (toQ power) global basis iter (toWeights b) t
    (by rw [finish];rfl) inside (by simpa only [mapVec,List.length_map] using width) progress limbs basisCanonical
  have transport := NEV_RowStep.active ops v power global basis iter b width finish inside globalBound
  have equal : (cursor,toWeights after)=(iter1,b1) := by
    have equality : ok (cont (cursor,toWeights after) : NEV_RowStep.Flow)=ok (cont (iter1,b1)) := by
      simpa only [run,step,bind_tc_ok,NEV_RowStep.mapFlow] using transport
    exact ControlFlow.cont.inj (Result.ok.inj equality)
  have eqCursor : cursor=iter1 := congrArg Prod.fst equal
  have eqWeights : toWeights after=b1 := congrArg Prod.snd equal
  subst iter1
  rw [← eqWeights] at successor
  exact ⟨start,endpoint,successor⟩
#print axioms next
end NEV_ReachedProgress
end
