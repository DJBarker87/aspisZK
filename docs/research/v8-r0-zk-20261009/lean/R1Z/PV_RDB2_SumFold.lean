import R1Z.PV_RDB2_SumControl
set_option autoImplicit false
noncomputable section
namespace PV_B1_SumFold
open Aeneas Aeneas.Std Result PV_B1_230 PV_B1_SumControl

def fold : List Q → Q → Result Q
  | [],sum => ok sum
  | x::xs,sum => do
    let next ← aspis_core.field.QM31.add sum x
    fold xs next

theorem read (h1 : Slice Q) (i : Usize) (h : i.val < h1.val.length) :
    Slice.index_usize h1 i = ok h1.val[i.val] := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]

theorem step (h1 : Slice Q) (i : Usize) (h : i.val < (Slice.len h1).val) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have big := (Slice.len h1).hSize
  omega

theorem finite (h1 : Slice Q) (fuel : Nat) (sum : Q) (i : Usize)
    (bound : i.val+fuel=(Slice.len h1).val) :
    PV_B1_SumControl.finite h1 fuel sum i = fold (h1.val.drop i.val) sum := by
  induction fuel generalizing sum i with
  | zero =>
    have hi : ¬i < Slice.len h1 := by
      change ¬ i.val < (Slice.len h1).val
      omega
    have hn : h1.val.drop i.val = [] := List.drop_eq_nil_of_le (by
      change h1.val.length ≤ i.val
      change i.val+0=h1.val.length at bound
      omega)
    simp only [PV_B1_SumControl.finite,dispatch,hi,if_false,hn,fold]
  | succ fuel ih =>
    have hi : i.val < (Slice.len h1).val := by omega
    have hs := step h1 i hi
    have hl : i.val < h1.val.length := hi
    rw [List.drop_eq_getElem_cons hl,fold]
    simp only [PV_B1_SumControl.finite,dispatch,
      show i < Slice.len h1 from hi,if_true,read h1 i hl,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hn
    rw [ih _ _ (by omega),hs]

theorem op230_source (h1 : Slice Q) :
    state_only_copy_helper_sum h1 =
      if Slice.len h1 = TRACE_ROWS then
        (do let s ← fold h1.val aspis_core.field.QM31.ZERO
            ok (some s))
      else ok none := by
  rw [PV_B1_SumControl.op230_source]
  split
  · rw [finite h1 (Slice.len h1).val _ 0#usize (by change 0+_= _; omega)]
    rfl
  · rfl
#print axioms read
#print axioms step
#print axioms finite
#print axioms op230_source
end PV_B1_SumFold
