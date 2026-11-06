import NLM_CopyFrames
set_option autoImplicit false
namespace NLM_CopyIteration
/-- One arbitrary indexed write is the step checked by the native window
probe. The invariant covers all previous cells and every untouched cell. -/
def Invariant {α : Type} (src before after : Nat → α) (start done : Nat) : Prop :=
 ∀ k,after k=if start≤k ∧ k<start+done then src k else before k

theorem zero {α : Type} (src before : Nat → α) (start : Nat) :
 Invariant src before before start 0 := by
 intro k
 rw [if_neg (by omega)]

theorem step {α : Type} (src before after : Nat → α) (start done : Nat)
 (h : Invariant src before after start done) :
 Invariant src before (KMX_CopyMeaning.write after (start+done) (src (start+done))) start (done+1) := by
 intro k
 unfold KMX_CopyMeaning.write
 by_cases same : k=start+done
 · subst k
   rw [if_pos rfl,if_pos (by omega)]
 · rw [if_neg same,h]
   by_cases old : start≤k ∧ k<start+done
   · rw [if_pos old,if_pos (by omega)]
   · rw [if_neg old,if_neg (by omega)]
#print zero
#print step
#print axioms zero
#print axioms step
end NLM_CopyIteration
