import PV_RJ4IDB_PowersControl
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_PowersBridge
open Aeneas Aeneas.Std Result ProverRwFull PV_RJ4IDB_PowersControl
variable [ExternalTypes] [ExternalFuns]

def finish {N : Usize} (r : Result (ProverRwP6PowersControl.Ret N)) : Result (Array W N) := do
  let (out,pending) ← r
  match pending with
  | none => ok out
  | some returned => ok returned

theorem step {N : Usize} (i : Usize) (h : i < N) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have big := N.hSize
  change i.val < N.val at h
  omega

theorem finite {N : Usize} (x : W) (fuel : Nat) (out : Array W N) (p : W) (i : Usize)
    (bound : i.val+fuel=N.val) :
    PV_RJ4IDB_PowersControl.finite x fuel out p i =
      finish (ProverRwP6PowersFinite.finite x fuel out p i) := by
  induction fuel generalizing out p i with
  | zero =>
    have hi : ¬ i<N := by change ¬i.val<N.val; omega
    simp only [PV_RJ4IDB_PowersControl.finite,ProverRwP6PowersFinite.finite,
      dispatch,ProverRwP6PowersControl.dispatch,hi,if_false,finish,bind_tc_ok] <;> rfl
  | succ fuel ih =>
    have hi : i<N := by change i.val<N.val; omega
    have hs := step i hi
    have hn : (Usize.wrapping_add i 1#usize).val+fuel=N.val := by omega
    simp only [PV_RJ4IDB_PowersControl.finite,ProverRwP6PowersFinite.finite,
      dispatch,ProverRwP6PowersControl.dispatch,hi,if_true]
    cases hr : Array.index_mut_usize out i with
    | fail e => simp only [hr,bind_tc_fail,finish]
    | div => simp only [hr,bind_tc_div,finish]
    | ok pair =>
      rcases pair with ⟨old,back⟩
      simp only [hr,bind_tc_ok]
      by_cases last : Usize.wrapping_add i 1#usize = N
      · have hz : fuel=0 := by rw [last] at hn; omega
        subst fuel
        simp only [last,lt_self_iff_false,if_false,if_true,
          PV_RJ4IDB_PowersControl.finite,dispatch,finish,bind_tc_ok] <;> rfl
      · have hlt : Usize.wrapping_add i 1#usize < N := by
          change (Usize.wrapping_add i 1#usize).val<N.val
          have neq : (Usize.wrapping_add i 1#usize).val ≠ N.val := by
            intro he; apply last; exact UScalar.eq_of_val_eq he
          omega
        simp only [last,hlt,if_true,if_false]
        cases hm : aspis_core.field.wide_exact.WideExact.mul p x with
        | fail e => simp only [hm,bind_tc_fail,finish] <;> rfl
        | div => simp only [hm,bind_tc_div,finish] <;> rfl
        | ok next =>
          simp only [hm,bind_tc_ok]
          exact ih (back p) next (Usize.wrapping_add i 1#usize) hn

/-- All N, arbitrary incoming field Result callbacks, every fail/div branch. -/
theorem complete (N : Usize) (x : W) :
    PV_RJ4IDB_PowersControl.powers N x = ProverRwP6PowersSource.weights.powers N x := by
  rw [PV_RJ4IDB_PowersControl.source,ProverRwP6PowersFinite.powers_finite]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro one ho
  exact finite x N.val _ _ 0#usize (by change 0+_= _; omega)

#print axioms step
#print axioms finite
#print axioms complete
end R1Z.PV_RJ4IDB_PowersBridge
