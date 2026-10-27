import RPu_FJa_SplitMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ExpandModel
open FIv_NativeValue (K)
/-- Symbolic coordinate fold in exactly the installed order. -/
def value : List K → Nat → (Nat → K) → (Nat → K)
  | [],_,f => f
  | c::cs,n,f => value cs (2*n) (FJa_SplitModel.fold c n f)
/-- Every coordinate doubles the live width and conserves mass. -/
theorem mass (cs : List K) (n : Nat) (f : Nat → K) :
    (∑ j∈Finset.range (2^cs.length*n),value cs n f j)=∑ i∈Finset.range n,f i := by
  induction cs generalizing n f with
  | nil => simp only [List.length_nil,pow_zero,one_mul,value]
  | cons c cs ih =>
    have eq : 2^(c::cs).length*n=2^cs.length*(2*n) := by
      simp only [List.length_cons,pow_succ];ring
    rw [eq,value,ih,FJa_SplitMass.value]
#print axioms mass
end AspisR1.FJa_ExpandModel
end
