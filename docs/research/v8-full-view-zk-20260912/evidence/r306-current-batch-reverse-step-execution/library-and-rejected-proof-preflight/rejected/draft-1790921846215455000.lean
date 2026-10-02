import AspisR305BatchReverseRaw
import AspisV8R19.R250PrivateBaseExecution

/-! Exact generated reverse-body execution against the pinned Aeneas library.
The selected-read and index premises are local invariants, not conclusions
about the complete source batch or its zero guard. -/
set_option autoImplicit false
namespace AspisV8R19.R306BatchReverseStepExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm
noncomputable section

abbrev ReverseRange := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

theorem wrapping_sub_one_val (n : Usize) (hn : 1 ≤ n.val) :
    (Usize.wrapping_sub n 1#usize).val = n.val - 1 := by
  rw [Usize.wrapping_sub_val_eq]
  have hb : n.val < UScalar.size .Usize := by
    simpa only [UScalar.size] using n.hBounds
  have h1 : (1#usize).val = 1 := by simp
  rw [h1]
  have he : n.val + (UScalar.size .Usize - 1) =
      (n.val - 1) + UScalar.size .Usize := by omega
  rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem reverse_next_done (iter : ReverseRange)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
        .ok (none, iter) := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, bind_tc_ok]
  have h : ¬ iter.iter.start.val < iter.iter.end.val := by omega
  trace_state
  simp [h]

theorem reverse_next_step (iter : ReverseRange)
    (hstep : iter.iter.start.val < iter.iter.end.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
        .ok (some (Usize.wrapping_sub iter.iter.end 1#usize),
          ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩) := by
  have he : 1 ≤ iter.iter.end.val := by omega
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, bind_tc_ok]
  simp only [hstep, decide_true, ↓reduceIte,
    core.iter.range.UScalarStep.backward_checked]
  simp only [show (1#usize).val = 1 from by simp, he, ↓reduceDIte, bind_tc_ok]
  have hp : Usize.ofNatCore (iter.iter.end.val - 1) (by scalar_tac) =
      Usize.wrapping_sub iter.iter.end 1#usize := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.ofNatCore_val_eq, wrapping_sub_one_val _ he]
  rw [hp]

theorem body2_done (xs : Slice U32) (px ox : alloc.vec.Vec U32)
    (iter : ReverseRange) (ix : U32)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    batch_loop2.body xs px iter ix ox = .ok (.done (ix, ox)) := by
  simp only [batch_loop2.body, reverse_next_done iter hstop, bind_tc_ok]

theorem body2_step (xs : Slice U32) (px ox : alloc.vec.Vec U32)
    (iter : ReverseRange) (x p v : M31Exact)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hp : px.val[(Usize.wrapping_sub (Usize.wrapping_sub iter.iter.end 1#usize)
        1#usize).val]? = some (encodeBase p))
    (hv : xs.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]? =
        some (encodeBase v))
    (ho : (Usize.wrapping_sub iter.iter.end 1#usize).val < ox.length) :
    batch_loop2.body xs px iter (encodeBase x) ox =
      .ok (.cont (⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩,
        encodeBase (x * v),
        ox.set (Usize.wrapping_sub iter.iter.end 1#usize) (encodeBase (p * x)))) := by
  have hout := spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec ox
      (Usize.wrapping_sub iter.iter.end 1#usize) ho)
  obtain ⟨⟨old, back⟩, hb, hval, hback⟩ := hout
  simp only [batch_loop2.body, reverse_next_step iter hstep, bind_tc_ok,
    lift, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize, hp,
    R250PrivateBaseExecution.mul_encoded, alloc.vec.Vec.index_mut_slice_index,
    hb, hback, Slice.index_usize, Slice.getElem?_Nat_eq,
    Slice.getElem?_Usize_eq, hv, bind_tc_ok]

theorem body3_eq_body2 (ys : Slice U32) (py oy : alloc.vec.Vec U32)
    (iter : ReverseRange) (iy : U32) :
    batch_loop3.body ys py iter iy oy = batch_loop2.body ys py iter iy oy := by
  rfl

#print axioms wrapping_sub_one_val
#print axioms reverse_next_done
#print axioms reverse_next_step
#print axioms body2_done
#print axioms body2_step
#print axioms body3_eq_body2
end
end AspisV8R19.R306BatchReverseStepExecution
