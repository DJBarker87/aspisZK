import NIX_ResidualCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ActiveFrames
open Aeneas Aeneas.Std Result
variable {Q : Type} [AddCommMonoid Q]

def step (sums : Fin 7 → Q) (coordinate : Fin 7) (value : Q) : Fin 7 → Q :=
 Function.update sums coordinate (sums coordinate+value)

def build (high : Nat → Q) (coordinate : Nat → Fin 7) : Nat → Fin 7 → Q
 | 0=>fun _=>0
 | n+1=>step (build high coordinate n) (coordinate n) (high n)

theorem frame (sums : Fin 7 → Q) (coordinate observed : Fin 7) (value : Q)
 (different : observed≠coordinate) : step sums coordinate value observed=sums observed := by
 simp only [step,Function.update_of_ne different]

theorem grouped (high : Nat → Q) (coordinate : Nat → Fin 7) (n : Nat) (i : Fin 7) :
 build high coordinate n i=∑ j∈Finset.range n,if coordinate j=i then high j else 0 := by
 induction n with
 | zero=>simp only [build,Finset.range_zero,Finset.sum_empty]
 | succ n ih=>
  rw [Finset.sum_range_succ]
  by_cases same : coordinate n=i
  · subst i
    simp [build,step,Function.update,ih]
  · simp only [build,step,Function.update_of_ne (Ne.symm same),ih,if_neg same,add_zero]

/-- The source cell's selected add is discharged in Lean; its two operands
are the SAME arbitrary pre-state bucket and high input observed by Kani. -/
theorem add_reply (a b : FIq_Native.field.QM31)
 (ha : FIv_NativeValue.Canon a) (hb : FIv_NativeValue.Canon b) :
 ∃ out,FIq_Native.field.QM31.add a b=ok out ∧ FIv_NativeValue.Canon out ∧
 FIv_NativeValue.decode out=FIv_NativeValue.decode a+FIv_NativeValue.decode b :=
 FIv_PreparedTotal.add a b ha hb

#print axioms frame
#print axioms grouped
#print axioms add_reply
end AspisR1.NIX_ActiveFrames
end
