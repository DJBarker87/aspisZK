import PV_RJ4IDB_NativePowers
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_PowersSafety
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_RJ4IDB_PowersControl
variable [ExternalTypes]

theorem increment {N : Usize} (i : Usize) (hi : i.val<N.val) :
 (Usize.wrapping_add i 1#usize).val=i.val+1 := by
 rw [Usize.wrapping_add_val_eq]
 change (i.val+1)%UScalar.size .Usize=i.val+1
 rw [Nat.mod_eq_of_lt]
 have hn := N.hSize
 omega

theorem index_restore {N : Usize} (out : Array W N) (i : Usize) (hi : i.val<N.val) :
 ∃ old, Array.index_mut_usize out i = ok (old,Aeneas.Std.Array.set out i) := by
 obtain ⟨v,hv⟩ := ProverRwP6ArrayRead.read out i hi
 unfold Array.index_mut_usize
 rw [hv]
 exact ⟨v,rfl⟩

theorem mul_total (ops : ExternalFuns) (p x : W) :
 ∃ q, @aspis_core.field.wide_exact.WideExact.mul _
 (PV_RJ4IDB_NativePowers.primitives ops) p x = ok q := by
 rw [PV_RJ4IDB_NativePowers.primitives_equal]
 obtain ⟨q,hq⟩ := ProverRwP6WideTotal.dictionary_mul p x
 exact ⟨q,hq⟩

theorem finite_total (ops : ExternalFuns) {N : Usize} (x : W) (fuel : Nat)
 (out : Array W N) (p : W) (i : Usize) (bound : i.val+fuel=N.val) :
 ∃ result, @finite _ (PV_RJ4IDB_NativePowers.primitives ops) N x fuel out p i = ok result := by
 letI : ExternalFuns := PV_RJ4IDB_NativePowers.primitives ops
 induction fuel generalizing out p i with
 | zero =>
   have hi : ¬i<N := by change ¬i.val<N.val; omega
   simp only [finite,dispatch,hi,if_false]
   exact ⟨out,rfl⟩
 | succ fuel ih =>
   have hi : i<N := by change i.val<N.val; omega
   obtain ⟨v,hv⟩ := index_restore out i hi
   have inc := increment i hi
   have b1 : (Usize.wrapping_add i 1#usize).val+fuel=N.val := by omega
   simp only [finite,dispatch,hi,if_true,hv,bind_tc_ok]
   split
   · obtain ⟨q,hq⟩ := mul_total ops p x
     rw [hq]
     exact ih _ _ _ b1
   · exact ih _ _ _ b1

#print axioms increment
#print axioms index_restore
#print axioms mul_total
#print axioms finite_total
end R1Z.PV_RJ4IDB_PowersSafety
