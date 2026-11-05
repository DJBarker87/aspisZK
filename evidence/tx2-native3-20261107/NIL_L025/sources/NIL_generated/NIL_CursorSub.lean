import NIL_FreshOps
set_option autoImplicit false
namespace NIL_CursorSub
open Aeneas Aeneas.Std Result

theorem value (a b : Usize) (h : b.val≤a.val) :
 (Usize.wrapping_sub a b).val=a.val-b.val := by
 rw [Usize.wrapping_sub_val_eq]
 have fit : a.val<UScalar.size .Usize := by rw [UScalar.size_def];exact a.bv.isLt
 have fitb : b.val<UScalar.size .Usize := by rw [UScalar.size_def];exact b.bv.isLt
 change (a.val+(UScalar.size .Usize-b.val))%UScalar.size .Usize=a.val-b.val
 rw [show a.val+(UScalar.size .Usize-b.val)=(a.val-b.val)+UScalar.size .Usize by omega,
  Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem source (a b : Usize) (h : b.val≤a.val) :
 (a-b : Result Usize)=ok (Usize.wrapping_sub a b) := by
 have total : ∃ c : Usize, (a-b : Result Usize)=ok c ∧ c.val=a.val-b.val := by
  apply WP.spec_imp_exists
  apply UScalar.sub_spec
  exact h
 obtain ⟨c,run,v⟩ := total
 have eq : c=Usize.wrapping_sub a b := UScalar.eq_of_val_eq (v.trans (value a b h).symm)
 exact run.trans (congrArg Result.ok eq)
#print axioms value
#print axioms source
end NIL_CursorSub
