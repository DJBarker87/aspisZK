import R1Z.ProverRwP6PowersFinite
import R1Z.ProverRwP6ArrayMutRead
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersRunTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersControl ProverRwP6PowersFinite
variable [ExternalTypes] [ExternalFuns]
theorem finite_total {N : Usize} (x : W) (fuel : Nat)
    (out : Array W N) (p : W) (i : Usize) (bound : i.val+fuel=N.val)
    (mul_total : ∀ a b : W, ∃ c, aspis_core.field.wide_exact.WideExact.mul a b = ok c) :
    ∃ result, finite x fuel out p i = ok result := by
  induction fuel generalizing out p i with
  | zero =>
    have cap : ¬ i<N := by change ¬i.val<N.val; omega
    exact ⟨(out,none),by simp only [finite,dispatch,cap,if_false]⟩
  | succ fuel ih =>
    have hi : i.val<N.val := by omega
    have test : i<N := hi
    obtain ⟨old,back,hr⟩ := ProverRwP6ArrayMutRead.read out i hi
    simp only [finite,dispatch,test,if_true,hr,bind_tc_ok]
    by_cases last : Usize.wrapping_add i 1#usize = N
    · simp only [last,if_true]
      exact ⟨_,rfl⟩
    · simp only [last,if_false]
      obtain ⟨p1,hp⟩ := mul_total p x
      simp only [hp,bind_tc_ok]
      apply ih
      have add : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
        rw [Usize.wrapping_add_val_eq]
        change (i.val+1)%UScalar.size .Usize=i.val+1
        apply Nat.mod_eq_of_lt
        have big := N.hSize
        omega
      omega
#print axioms finite_total
end R1Z.ProverRwP6PowersRunTotal
