import PV_B1_258_Funs
import PV_B1_Loop
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleControl
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258
abbrev Q := aspis_core.field.QM31
abbrev Rows := Slice (Array (Array Q 2#usize) 2#usize)
abbrev Src := all_slots_clear_loop0

def dispatch (recur : Bool → Usize → Result Bool) (values : Rows)
    (masks : Array U16 64#usize) (chi : Q) (clear : Bool) (row : Usize) : Result Bool := do
  if row < Slice.len values then
    let mask ← Array.index_usize masks (Usize.wrapping_shr row 4#u32)
    let active := (mask &&& U16.wrapping_shl 1#u16 (UScalar.cast .U32 (row &&& 15#usize))) != 0#u16
    let next ← all_slots_clear_loop0_loop0 values chi clear row active 0#usize
    recur next (Usize.wrapping_add row 1#usize)
  else ok clear

theorem source_unfold (values : Rows) (masks : Array U16 64#usize)
    (chi : Q) (clear : Bool) (row : Usize) :
    Src values masks chi clear row = dispatch (Src values masks chi) values masks chi clear row := by
  unfold Src all_slots_clear_loop0
  rw [PV_B1_Loop.bind]
  unfold all_slots_clear_loop0.body dispatch
  dsimp only
  by_cases h : row < Slice.len values
  · simp only [h,if_true,lift,bind_tc_ok,bind_assoc_eq]
  · simp only [h,if_false,bind_tc_ok]

theorem dispatch_congr (values : Rows) (masks : Array U16 64#usize)
    (chi : Q) (clear : Bool) (row : Usize)
    (left right : Bool → Usize → Result Bool)
    (same : ∀ c, left c (Usize.wrapping_add row 1#usize) =
      right c (Usize.wrapping_add row 1#usize)) :
    dispatch left values masks chi clear row = dispatch right values masks chi clear row := by
  unfold dispatch
  split
  · repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    apply same
  · rfl

def finite (values : Rows) (masks : Array U16 64#usize) (chi : Q) : Nat → Bool → Usize → Result Bool
  | 0,clear,row => dispatch (fun _ _ => .div) values masks chi clear row
  | fuel+1,clear,row => dispatch (finite values masks chi fuel) values masks chi clear row

theorem loop_finite (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (fuel : Nat) (clear : Bool) (row : Usize)
    (bound : row.val+fuel=(Slice.len values).val) :
    Src values masks chi clear row = finite values masks chi fuel clear row := by
  induction fuel generalizing clear row with
  | zero =>
    have cap : ¬row < Slice.len values := by change ¬row.val<(Slice.len values).val; omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_false]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ _ _ = dispatch _ _ _ _ _ _
    apply dispatch_congr
    intro c
    apply ih
    have add : (Usize.wrapping_add row 1#usize).val=row.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (row.val+1)%UScalar.size .Usize=row.val+1
      rw [Nat.mod_eq_of_lt]
      have big := (Slice.len values).hSize
      omega
    omega

theorem op258_source (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    all_slots_clear values masks chi =
      finite values masks chi (Slice.len values).val true 0#usize := by
  exact loop_finite values masks chi (Slice.len values).val true 0#usize
    (by change 0+_= _; omega)
#print axioms source_unfold
#print axioms dispatch_congr
#print axioms loop_finite
#print axioms op258_source
end PV_B1_PoleControl
