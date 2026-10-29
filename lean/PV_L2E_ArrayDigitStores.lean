import PV_L2E_ArrayDigits
import PV_L2E_ArrayForward
set_option autoImplicit false
namespace PV_L2E_ArrayDigitStores
open PV_L2E_ArrayMemory PV_L2E_ArrayForward

/-- The source's quotient AND digit arrays, including every remainder store. -/
def run (width : Nat) : Nat → Nat → Memory → Memory → Memory × Memory
  | _,0,q,d => (q,d)
  | i,n+1,q,d =>
    let p := PV_L2E_ArrayDivision.run width 0 q
    run width (i+1) n p.1 (store d i p.2)

theorem digit_frame (width i n : Nat) (q d : Memory) (j : Nat)
    (outside : j < i ∨ i+n≤j) : (run width i n q d).2 j=d j := by
  induction n generalizing i q d with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih _ _ _ (by omega),store_elsewhere d i j _ (by omega)]

theorem complete (width i n : Nat) (q d : Memory) :
    (run width i n q d).1=(PV_L2E_ArrayDigits.run width n q).1 ∧
    slice (run width i n q d).2 i n=(PV_L2E_ArrayDigits.run width n q).2 := by
  induction n generalizing i q d with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have ht := ih (i+1) (PV_L2E_ArrayDivision.run width 0 q).1
      (store d i (PV_L2E_ArrayDivision.run width 0 q).2)
    have hw := digit_frame width (i+1) n (PV_L2E_ArrayDivision.run width 0 q).1
      (store d i (PV_L2E_ArrayDivision.run width 0 q).2) i (Or.inl (by omega))
    rw [store_here] at hw
    simp only [run,PV_L2E_ArrayDigits.run,slice]
    exact ⟨ht.1,by rw [hw,ht.2]⟩

#print axioms digit_frame
#print axioms complete
end PV_L2E_ArrayDigitStores
