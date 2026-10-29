import LPf_BaseMultiply
set_option autoImplicit false
namespace NDH_Pow5
open Aeneas Aeneas.Std Result
open FIo_Native.aspis_core.field

def reference (x : U32) : Result U32 := do
  let square ← M31.mul x x
  let fourth ← M31.mul square square
  M31.mul fourth x

theorem fifth_mod (x p : Nat) :
    (((x*x)%p*((x*x)%p))%p*x)%p=x^5%p := by
  calc
    _ = ((x*x)*(x*x)*x)%p := by simp only [Nat.mul_mod,Nat.mod_mod]
    _ = x^5%p := by congr 1; ring

theorem value (x : U32) : ∃ square fourth out,
    M31.mul x x=ok square ∧ M31.mul square square=ok fourth ∧
    M31.mul fourth x=ok out ∧ reference x=ok out ∧
    square.val<2147483647 ∧ fourth.val<2147483647 ∧
    out.val=x.val^5%2147483647 ∧ out.val<2147483647 := by
  obtain ⟨square,squareRun,squareValue,squareBound⟩ := AspisR1.LPf_BaseMultiply.source x x
  obtain ⟨fourth,fourthRun,fourthValue,fourthBound⟩ := AspisR1.LPf_BaseMultiply.source square square
  obtain ⟨out,outRun,outValue,outBound⟩ := AspisR1.LPf_BaseMultiply.source fourth x
  refine ⟨square,fourth,out,squareRun,fourthRun,outRun,?_,squareBound,fourthBound,?_,outBound⟩
  · simp only [reference,squareRun,fourthRun,outRun,bind_tc_ok]
  · rw [outValue,fourthValue,squareValue]
    exact fifth_mod x.val 2147483647

#print axioms fifth_mod
#print axioms value
end NDH_Pow5
