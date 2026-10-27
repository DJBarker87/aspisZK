import RPu_FJa_ArrayUpdate
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SplitModel
open FIv_NativeValue (K)
/-- Two writes of the installed descending split, in source order. -/
def step (c : K) (f : Nat → K) (i : Nat) : Nat → K :=
  Function.update (Function.update f (2*i) (f i-c*f i)) (2*i+1) (c*f i)
def fold (c : K) : Nat → (Nat → K) → (Nat → K)
  | 0,f => f
  | n+1,f => fold c n (step c f n)
theorem lower (c : K) (f : Nat → K) (i j : Nat) (hj : j < i) : step c f i j=f j := by
  unfold step
  rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
theorem left (c : K) (f : Nat → K) (i : Nat) : step c f i (2*i)=f i-c*f i := by
  unfold step
  rw [Function.update_of_ne (by omega),Function.update_self]
theorem right (c : K) (f : Nat → K) (i : Nat) : step c f i (2*i+1)=c*f i := by
  unfold step
  exact Function.update_self _ _ _
theorem outside (c : K) (f : Nat → K) (i j : Nat) (hj : 2*i+1<j) : step c f i j=f j := by
  unfold step
  rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
#print axioms lower
#print axioms left
#print axioms right
#print axioms outside
end AspisR1.FJa_SplitModel
end
