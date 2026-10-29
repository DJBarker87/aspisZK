import PV_B3P_UsizeLoop9227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- Element offsets within one valid non-ZST array allocation. This is an
abstract Rust pointer region, not a pointer-to-integer cast. The compiler /
intrinsic transport stays at V370. The actual caller has exactly four slots. -/
structure SlotPointer13 where
  region : Nat
  index : Usize

def slot_end13 (region : Nat) : SlotPointer13 := ⟨region,4#usize⟩
def slot_same13 (left right : SlotPointer13) : Bool :=
  left.region == right.region && left.index == right.index

theorem same_region_end13 (region : Nat) (index : Usize) :
    slot_same13 ⟨region,index⟩ (slot_end13 region) = (index == 4#usize) := by
  simp only [slot_same13,slot_end13,beq_self_eq_true,Bool.true_and]

/-- The forward, non-ZST IterMut::next source branch. A returned index is the
exclusive slot token consumed by the caller's write; no mutable ref escapes. -/
def slice_next13 (index : Usize) : Result (Option Usize × Usize) :=
  if index = 4#usize then .ok (none,index)
  else .ok (some index,Usize.wrapping_add index 1#usize)

/-- core::iter::adapters::enumerate::next: the count increments only on Some. -/
def enumerate_next13 (index count : Usize) :
    Result (Option (Usize × Usize) × Usize × Usize) := do
  let (item,next) ← slice_next13 index
  match item with
  | none => .ok (none,next,count)
  | some slot => .ok (some (count,slot),next,Usize.wrapping_add count 1#usize)

theorem enumerate_finish13 : enumerate_next13 4#usize 4#usize = .ok (none,4#usize,4#usize) := rfl

theorem enumerate_step13 (index : Usize) (bound : index.val < 4) :
    enumerate_next13 index index = .ok
      (some (index,index),Usize.wrapping_add index 1#usize,Usize.wrapping_add index 1#usize) := by
  have different : index ≠ 4#usize := by scalar_tac
  simp only [enumerate_next13,slice_next13,different,if_false,bind_tc_ok]

theorem cursor_increment13 (index : Usize) (bound : index.val < 4) :
    (Usize.wrapping_add index 1#usize).val = index.val+1 :=
  PV_B3P_Offset226V3.add_value index 1#usize (by
    change index.val+1 < UScalar.size .Usize
    have h4 : (4 : Nat) < UScalar.size .Usize := by scalar_tac
    omega)

/-- Explicit empty iterator cleanup. Its two pointer fields and PhantomData
have no user destructor; data stores occur only in the consuming callback. -/
def slice_iterator_drop13 (_index _count : Usize) : Result Unit := .ok ()
theorem slice_iterator_drop_total13 (index count : Usize) :
    slice_iterator_drop13 index count = .ok () := rfl

#print axioms same_region_end13
#print axioms enumerate_finish13
#print axioms enumerate_step13
#print axioms cursor_increment13
#print axioms slice_iterator_drop_total13
end PV_B3P_Binding13227
