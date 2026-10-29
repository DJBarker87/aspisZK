import PV_L2E_ArrayDivisionTrace
import PV_L2E_DigitsValue
set_option autoImplicit false
namespace PV_L2E_ArrayDigits
open PV_L2E_ArrayMemory PV_L2D_DivisionBounds

/-- Repeated direct-index array division, retaining both the whole quotient
array and every remainder digit. Each pass starts at remainder zero. -/
def run (width : Nat) : Nat → Memory → Memory × List Nat
  | 0,a => (a,[])
  | n+1,a =>
    let p := PV_L2E_ArrayDivision.run width 0 a
    let tail := run width n p.1
    (tail.1,p.2::tail.2)

theorem complete (width n : Nat) (a : Memory) :
    backwards (run width n a).1 width=(PV_L2E_DigitsTrace.run n (backwards a width)).quotient ∧
    (run width n a).2=(PV_L2E_DigitsTrace.run n (backwards a width)).digits := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have hp := PV_L2E_ArrayDivision.complete width 0 a
    have hq := congrArg Prod.fst hp
    have hr := congrArg Prod.snd hp
    have ht := ih (PV_L2E_ArrayDivision.run width 0 a).1
    simp only [run,PV_L2E_DigitsTrace.run,PV_L2E_DivisionTrace.complete_value]
    rw [length] at *
    rw [hq] at ht
    exact ⟨ht.1,by rw [hr,ht.2]⟩

theorem digit_count (width n : Nat) (a : Memory) : (run width n a).2.length=n := by
  rw [(complete width n a).2,PV_L2E_DigitsTrace.digit_count]

theorem residue (width n : Nat) (a : Memory) (small : ∀ i,i<width → a i<B) :
    PV_L2E_CarryValue.value (run width n a).2=PV_L2E_WordRank.rank (backwards a width)%P^n := by
  rw [(complete width n a).2]
  exact PV_L2E_DigitsValue.residue n _ (bounds a width small)

#print axioms complete
#print axioms digit_count
#print axioms residue
end PV_L2E_ArrayDigits
