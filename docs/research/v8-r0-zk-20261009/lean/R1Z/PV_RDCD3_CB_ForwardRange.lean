import R1Z.PV_RDCD3_ReverseRange
set_option autoImplicit false
namespace R1Z.PV_RDCD3_CB_ForwardRange
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize
def between (i stop : Usize) : Range := ⟨i,stop⟩
def advance (i : Usize) : Usize := Usize.wrapping_add i 1#usize
abbrev next := core.iter.range.IteratorRange.next core.iter.range.StepUsize

theorem advance_val (i stop : Usize) (bound : i.val < stop.val) :
    (advance i).val = i.val+1 := by
  rw [advance,Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  rw [UScalar.size]
  have h := stop.hBounds
  omega
theorem next_done (i stop : Usize) (bound : stop.val ≤ i.val) :
    next (between i stop) = .ok (none,between i stop) := by
  simp [next,between,core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt,show ¬i.val<stop.val from by omega]
theorem next_step (i stop : Usize) (bound : i.val < stop.val) :
    next (between i stop) = .ok (some i,between (advance i) stop) := by
  have le : i.val+1 ≤ UScalar.max .Usize := by
    rw [UScalar.max]
    have h := stop.hBounds
    omega
  have lt : i.val < UScalar.max .Usize := by omega
  simp [next,between,core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt,core.iter.range.UScalarStep.forward_checked,
    bound,le,lt]
  apply UScalar.eq_of_val_eq
  exact (advance_val i stop bound).symm
#print axioms advance_val
#print axioms next_done
#print axioms next_step
end R1Z.PV_RDCD3_CB_ForwardRange
