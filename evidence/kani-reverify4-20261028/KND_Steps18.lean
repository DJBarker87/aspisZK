import KND_Composition
set_option autoImplicit false
namespace KND_Steps18
open KND_Schedule KND_Composition
def steps : List Step := [⟨"weight3",760,1768,16⟩,⟨"weight4",776,1768,16⟩,⟨"weight5",792,1768,16⟩]
theorem reachable : ∀ s ∈ steps, s ∈ schedule := by decide
theorem capacity : ∀ s ∈ steps, s.len + s.size ≤ s.cap := by decide
theorem bytes (s : Step) (_reachable : s ∈ steps) (before value : State)
 (j : Nat) (bound : j<s.len+s.size) :
 model s before value j = if j<s.len then before j else value (j-s.len) :=
 byte_law s before value j bound
#print axioms reachable
#print axioms capacity
#print axioms bytes
end KND_Steps18
