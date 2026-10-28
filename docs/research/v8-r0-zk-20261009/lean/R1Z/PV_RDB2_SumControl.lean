import R1Z.PV_RDB2_230_Funs
import R1Z.PV_RDB2_Loop
set_option autoImplicit false
noncomputable section
namespace PV_B1_SumControl
open Aeneas Aeneas.Std Result ControlFlow PV_B1_230
abbrev Q := aspis_core.field.QM31
abbrev Src := state_only_copy_helper_sum_loop

def dispatch (recur : Q → Usize → Result Q) (h1 : Slice Q)
    (sum : Q) (i : Usize) : Result Q := do
  if i < Slice.len h1 then
    let q ← Slice.index_usize h1 i
    let next ← aspis_core.field.QM31.add sum q
    recur next (Usize.wrapping_add i 1#usize)
  else ok sum

theorem source_unfold (h1 : Slice Q) (sum : Q) (i : Usize) :
    Src h1 sum i = dispatch (Src h1) h1 sum i := by
  unfold Src state_only_copy_helper_sum_loop
  rw [PV_B1_Loop.bind]
  unfold state_only_copy_helper_sum_loop.body dispatch
  dsimp only
  by_cases h : i < Slice.len h1
  · simp only [h,if_true,bind_assoc_eq,lift,bind_tc_ok]
  · simp only [h,if_false,bind_tc_ok]

theorem dispatch_congr (h1 : Slice Q) (sum : Q) (i : Usize)
    (left right : Q → Usize → Result Q)
    (same : ∀ a, left a (Usize.wrapping_add i 1#usize) =
      right a (Usize.wrapping_add i 1#usize)) :
    dispatch left h1 sum i = dispatch right h1 sum i := by
  unfold dispatch
  split
  · repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    apply same
  · rfl

def finite (h1 : Slice Q) : Nat → Q → Usize → Result Q
  | 0,sum,i => dispatch (fun _ _ => .div) h1 sum i
  | fuel+1,sum,i => dispatch (finite h1 fuel) h1 sum i

theorem loop_finite (h1 : Slice Q) (fuel : Nat) (sum : Q) (i : Usize)
    (bound : i.val+fuel=(Slice.len h1).val) :
    Src h1 sum i = finite h1 fuel sum i := by
  induction fuel generalizing sum i with
  | zero =>
    have cap : ¬ i < Slice.len h1 := by
      change ¬ i.val < (Slice.len h1).val
      omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_false]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ = dispatch _ _ _ _
    apply dispatch_congr
    intro a
    apply ih
    have add : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      rw [Nat.mod_eq_of_lt]
      have big := (Slice.len h1).hSize
      omega
    omega

theorem op230_source (h1 : Slice Q) :
    state_only_copy_helper_sum h1 =
      if Slice.len h1 = TRACE_ROWS then
        (do let s ← finite h1 (Slice.len h1).val aspis_core.field.QM31.ZERO 0#usize
            ok (some s))
      else ok none := by
  unfold state_only_copy_helper_sum
  dsimp only
  exact congrArg
    (fun r : Result Q =>
      if Slice.len h1 = TRACE_ROWS then
        (do let s ← r; ok (some s)) else ok none)
    (loop_finite h1 (Slice.len h1).val aspis_core.field.QM31.ZERO 0#usize
      (by change 0+_= _; omega))
#print axioms source_unfold
#print axioms dispatch_congr
#print axioms loop_finite
#print axioms op230_source
end PV_B1_SumControl
