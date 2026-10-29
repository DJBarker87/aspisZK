import PV_L2E_CarryTrace
set_option autoImplicit false
namespace PV_L2E_CarryValue
open PV_L2D_DivisionBounds PV_L2E_CarryTrace

/-- Little-endian positional interpretation, used symbolically. -/
def value : List Nat → Nat
  | [] => 0
  | d::ds => d+P*value ds

theorem reconstruct (i a : Nat) (ds : List Nat) :
    value (run i a ds).1.1 + P^ds.length*(run i a ds).1.2 = value ds+a := by
  induction ds generalizing i a with
  | nil => simp [run,value]
  | cons d ds ih =>
    have ht := ih (i+1) ((d+a)/P)
    have hd := Nat.mod_add_div (d+a) P
    simp only [run,value,List.length_cons,pow_succ]
    nlinarith

theorem value_bound (ds : List Nat) (hd : ∀ d∈ds,d<P) :
    value ds<P^ds.length := by
  induction ds with
  | nil => simp [value]
  | cons d ds ih =>
    have hh := hd d (by simp)
    have ht := ih (fun x hx => hd x (by simp [hx]))
    simp only [value,List.length_cons,pow_succ]
    have hp : 0<P := by decide
    nlinarith

/-- On wrap, the new low digits are strictly below the addend. This proves
that the second source add cannot wrap after a small first addend. -/
theorem wrapped_value_lt (i a : Nat) (ds : List Nat)
    (hd : ∀ d∈ds,d<P) (wrap : (run i a ds).1.2=1) :
    value (run i a ds).1.1<a := by
  have h := reconstruct i a ds
  have hb := value_bound ds hd
  rw [wrap,Nat.mul_one] at h
  omega

theorem no_wrap_of_small_sum (i a : Nat) (ds : List Nat)
    (small : value ds+a<P^ds.length) : (run i a ds).1.2=0 := by
  have h := reconstruct i a ds
  have hp : 0<P^ds.length := pow_pos (by decide : 0<P) _
  nlinarith

#print axioms reconstruct
#print axioms value_bound
#print axioms wrapped_value_lt
#print axioms no_wrap_of_small_sum
end PV_L2E_CarryValue
