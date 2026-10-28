import R1Z.PV_RDEA_ActualNameLoop
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_ActualNameFinite
variable [ExternalTypes] [ExternalFuns]
open PV_RDEA_ActualNameLoop

theorem loop_finite (digest : Array U8 32#usize) (n : Nat) (acc : String) (i : Usize)
    (bound : i.val+n=32) :
    aspis_prover.state_only_entropy.reservation_name digest acc i = finite digest n acc i := by
  induction n generalizing acc i with
  | zero =>
    have stop : i=32#usize := by apply UScalar.eq_of_val_eq; simpa using bound
    subst i
    exact PV_RDEA_ActualReservation.at_end digest acc
  | succ n ih =>
    have go : i≠32#usize := by intro h; subst i; change 32+(n+1)=32 at bound; omega
    have add : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      apply Nat.mod_eq_of_lt
      have large := (32#usize).hSize
      change 32<UScalar.size .Usize at large
      omega
    rw [step digest acc i go]
    simp only [finite]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro after called
    exact ih after _ (by omega)

theorem start (digest : Array U8 32#usize) (acc : String) :
    aspis_prover.state_only_entropy.reservation_name digest acc 0#usize =
      finite digest 32 acc 0#usize := loop_finite digest 32 acc 0#usize rfl

#print axioms loop_finite
#print axioms start
end R1Z.PV_RDEA_ActualNameFinite
