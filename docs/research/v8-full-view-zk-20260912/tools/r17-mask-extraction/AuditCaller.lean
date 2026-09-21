import AspisR17MaskSource.Funs

open Aeneas.Std Result
namespace AspisR17MaskSource

/-- The previous schematic body is definitionally the actual generated
closure, not merely a matching success case. The unused index is retained. -/
theorem actual_closure_body (c : r17_structured_g.mixing_row.closure) (i : Usize) :
    r17_structured_g.mixing_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i =
      AspisV8R17.MaskClosureWriteback.powerCallMut field.QM31.mul c := by
  rfl

theorem actual_closure_closed (power node : field.QM31) (i : Usize) :
    AspisV8R17.MaskClosureWriteback.finishCall
      (r17_structured_g.mixing_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        (power, node) i) = (do
          let next ← field.QM31.mul power node
          ok (power, (next, node))) := by
  rw [actual_closure_body]
  exact AspisV8R17.MaskClosureWriteback.powerCallMut_closed _ _ _

/-- The adapter instantiated with the generated closure emits the OLD power
and stores the NEW power. This includes multiplication failure/divergence;
the range-next premise is explicit, not a claim about the whole traversal. -/
theorem actual_map_step
    (iter nextIter : core.ops.range.Range Usize) (i : Usize)
    (power node : field.QM31)
    (hi : (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize).next iter =
      ok (some i, nextIter)) :
    IteratorCompat.mapNext
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      r17_structured_g.mixing_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      ⟨iter, (power, node)⟩ = (do
        let next ← field.QM31.mul power node
        ok (some power, (⟨nextIter, (next, node)⟩ :
          core.iter.adapters.map.Map (core.ops.range.Range Usize)
            r17_structured_g.mixing_row.closure))) := by
  change core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
    ok (some i, nextIter) at hi
  simp only [IteratorCompat.mapNext, hi, bind_tc_ok]
  change (do
    let (value, updated) ← AspisV8R17.MaskClosureWriteback.finishCall
      (r17_structured_g.mixing_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        (power, node) i)
    ok (some value, (⟨nextIter, updated⟩ :
      core.iter.adapters.map.Map (core.ops.range.Range Usize)
        r17_structured_g.mixing_row.closure))) = _
  rw [actual_closure_closed]
  cases h : field.QM31.mul power node <;> simp [h]

#print axioms actual_closure_body
#print axioms actual_closure_closed
#print axioms actual_map_step
#print axioms r17_structured_g.mixing_row
#print axioms r17_structured_g.mask_weights_loop0_loop0
#print axioms r17_structured_g.mask_weights_loop0
#print axioms r17_structured_g.mask_weights_loop1_loop0
#print axioms r17_structured_g.mask_weights_loop1
#print axioms r17_structured_g.mask_weights
end AspisR17MaskSource
