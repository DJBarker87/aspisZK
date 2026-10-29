import PV_L2E_ArrayForward
import PV_L2E_CarryValue
set_option autoImplicit false
namespace PV_L2E_ArrayCarry
open PV_L2E_ArrayMemory PV_L2E_ArrayForward PV_L2D_DivisionBounds

/-- Direct indexed mutation in add_small_base_p, ascending through all slots.
The addend is updated after the store exactly as in the source. -/
def run : Nat → Nat → Nat → Memory → Memory × Nat
  | _,0,c,a => (a,c)
  | i,n+1,c,a =>
    let sum := a i+c
    run (i+1) n (sum/P) (store a i (sum%P))

theorem frame (i n c : Nat) (a : Memory) (j : Nat) (outside : j < i ∨ i+n≤j) :
    (run i n c a).1 j=a j := by
  induction n generalizing i c a with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih _ _ _ (by omega),store_elsewhere a i j _ (by omega)]

theorem complete (i n c : Nat) (a : Memory) :
    (slice (run i n c a).1 i n,(run i n c a).2)=
      (PV_L2E_CarryTrace.run i c (slice a i n)).1 := by
  induction n generalizing i c a with
  | zero => rfl
  | succ n ih =>
    have ht := ih (i+1) ((a i+c)/P) (store a i ((a i+c)%P))
    rw [store_outside a (i+1) n i _ (Or.inl (by omega))] at ht
    have hw := frame (i+1) n ((a i+c)/P) (store a i ((a i+c)%P)) i (Or.inl (by omega))
    rw [store_here] at hw
    simp only [run,slice,PV_L2E_CarryTrace.run]
    rw [hw]
    exact congrArg (fun p : List Nat × Nat => ((a i+c)%P::p.1,p.2)) ht

#print axioms frame
#print axioms complete
end PV_L2E_ArrayCarry
