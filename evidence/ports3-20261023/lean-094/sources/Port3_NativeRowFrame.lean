import Port3_QueryStage
import Aeneas.Std.RangeIter

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeRowFrame
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_RowsInstall (toBW fromBW toK)

def push (b : verifier.BatchedWeights) (j : Usize) (q : aspis_core.field.QM31) (m : U32) :
    Result verifier.BatchedWeights := do
  let out ← S7Kani2OwnedPush.push_owned (toBW b) j (toK q) m
  ok (fromBW out)

def install (ops : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  {ops with op14 := push}

theorem push_fields (b out : verifier.BatchedWeights) (j : Usize)
    (q : aspis_core.field.QM31) (m : U32) (bound : j.val<b.raw.val.length)
    (h : push b j q m=ok out) :
    out.raw.val.length=b.raw.val.length ∧ out.terms=b.terms := by
  unfold push at h
  obtain ⟨mid,run,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have fields := Port3_PushFrame.push_fields (toBW b) mid j (toK q) m bound run
  cases Result.ok.inj h
  exact fields

/-- The actual native row body preserves the raw allocation and terms on a
successful active step, with its emitted wrapping trace offsets retained. -/
theorem body_fields (ops : Port3_NativeQueryBody.Ops)
    (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
    (next width : Usize) (basis : Array U32 256#usize)
    (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights)
    (active : iter.start.val < iter.end.val) (bound : iter.end.val≤b.raw.val.length)
    (out : ControlFlow (core.ops.range.Range Usize × verifier.BatchedWeights) verifier.BatchedWeights)
    (h : Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1.body
      (install ops) v q next width basis iter b=ok out) :
    ∃ iter1 b1, out=cont (iter1,b1) ∧ iter1.start.val=iter.start.val+1 ∧
      iter1.end=iter.end ∧ b1.raw.val.length=b.raw.val.length ∧ b1.terms=b.terms := by
  obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro a b; rfl) iter active)
  subst o
  unfold Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1.body at h
  rw [run] at h
  simp only [bind_tc_ok] at h
  obtain ⟨m,hm,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨b1,hpush,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have fields := push_fields b b1 iter.start q m (by omega) hpush
  iterate 9 obtain ⟨x,hx,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  exact ⟨iter1,b1,(Result.ok.inj h).symm,hs,he,fields⟩

#print axioms push_fields
#print axioms body_fields
end AspisR1.Port3_NativeRowFrame
end
