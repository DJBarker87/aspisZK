import PV_L2E_ArrayMemory
set_option autoImplicit false
namespace PV_L2E_ArrayDivision
open PV_L2E_ArrayMemory PV_L2D_DivisionBounds

/-- Exactly the direct-index reverse loop: decrement, read, form dividend,
store the quotient, update remainder, continue. Memory outside the array is
kept solely to state the frame law. The bounds guards are proved separately. -/
def run : Nat → Nat → Memory → Memory × Nat
  | 0,r,a => (a,r)
  | n+1,r,a =>
    let d := step r (a n)
    run n d.remainder (store a n d.quotient)

theorem frame (n r : Nat) (a : Memory) (j : Nat) (outside : n≤j) :
    (run n r a).1 j=a j := by
  induction n generalizing r a with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih _ _ (by omega),store_elsewhere a n j _ (by omega)]

/-- Every quotient store survives the remaining iterations, and the resulting
array in traversal order is the complete list pass, not only its remainder. -/
theorem complete (n r : Nat) (a : Memory) :
    (backwards (run n r a).1 n,(run n r a).2)=pass r (backwards a n) := by
  induction n generalizing r a with
  | zero => rfl
  | succ n ih =>
    have ht := ih (step r (a n)).remainder (store a n (step r (a n)).quotient)
    have hw := frame n (step r (a n)).remainder
      (store a n (step r (a n)).quotient) n (by omega)
    rw [store_here] at hw
    rw [lower_unchanged a n n _ (by omega)] at ht
    simp only [run,backwards,pass]
    rw [hw]
    exact congrArg (fun p : List Nat × Nat => ((step r (a n)).quotient::p.1,p.2)) ht

#print axioms frame
#print axioms complete
end PV_L2E_ArrayDivision
