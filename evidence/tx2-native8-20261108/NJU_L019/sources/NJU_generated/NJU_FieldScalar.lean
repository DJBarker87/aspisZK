import NJU_BadWindow
set_option autoImplicit false
namespace NJU_FieldScalar
open Aeneas Aeneas.Std Result

def start (i : Usize) (small : i.val<64) : Usize :=
 Usize.ofNat (i.val*32) (by scalar_tac)
def next (i : Usize) (small : i.val<64) : Usize :=
 Usize.ofNat (i.val+1) (by scalar_tac)
def stop (i : Usize) (small : i.val<64) : Usize :=
 Usize.ofNat ((i.val+1)*32) (by scalar_tac)

theorem checked (i : Usize) (small : i.val<64) :
 (i*32#usize : Result Usize)=ok (start i small) ∧
 (i+1#usize : Result Usize)=ok (next i small) ∧
 ((next i small)*32#usize : Result Usize)=ok (stop i small) := by
 unfold start next stop
 constructor
 · scalar_tac
 constructor <;> scalar_tac

/-- Exact emitted abort at a None decoder reply. These are local checked
operation clauses, not a positive-root endpoint/success premise. -/
theorem abort_none {T : Type} (decode : Slice U8 → Result (Option T))
 (bytes selected : Slice U8) (i : Usize) (small : i.val<64)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=start i small,«end»:=stop i small}=ok selected)
 (decoded : decode selected=ok none) :
 AspisR1WeightsFieldCurrent.weights.field decode bytes i=fail .panic := by
 obtain ⟨mul0,add1,mul1⟩:=checked i small
 unfold AspisR1WeightsFieldCurrent.weights.field
 rw [mul0,bind_tc_ok,add1,bind_tc_ok,mul1,bind_tc_ok,range,bind_tc_ok,decoded]
 rfl

#print axioms checked
#print axioms abort_none
end NJU_FieldScalar
