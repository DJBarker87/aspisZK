import R1Z.ProverRwP6PowersControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersFinite
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull ProverRwP6PowersControl
variable [ExternalTypes] [ExternalFuns]
def finite {N : Usize} (x : W) : Nat → Array W N → W → Usize → Result (Ret N)
  | 0,out,p,i => dispatch (fun _ _ _ => .div) x out p i
  | fuel+1,out,p,i => dispatch (finite x fuel) x out p i

theorem loop_finite {N : Usize} (x : W) (fuel : Nat)
    (out : Array W N) (p : W) (i : Usize) (bound : i.val+fuel=N.val) :
    Src x out p i = finite x fuel out p i := by
  induction fuel generalizing out p i with
  | zero =>
    have cap : ¬ i<N := by change ¬i.val<N.val; omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_false]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ _ = dispatch _ _ _ _ _
    apply dispatch_congr
    intro a b
    apply ih
    have add : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      rw [Nat.mod_eq_of_lt]
      have big := N.hSize
      omega
    omega

theorem powers_finite (N : Usize) (x : W) :
    ProverRwP6PowersSource.weights.powers N x = (do
      let zero ← aspis_core.field.wide_exact.WideExact.ZERO
      let one ← ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE
      let (out,pending) ← finite x N.val (Array.repeat N zero) one 0#usize
      match pending with
      | none => ok out
      | some returned => ok returned) := by
  unfold ProverRwP6PowersSource.weights.powers
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro one ho
  exact congrArg (fun r : Result (Ret N) => do
    let (out,pending) ← r
    match pending with
    | none => ok out
    | some returned => ok returned)
    (loop_finite x N.val (Array.repeat N zero) one 0#usize (by change 0+_= _; omega))

#print axioms loop_finite
#print axioms powers_finite
end R1Z.ProverRwP6PowersFinite
