import KND_Composition
set_option autoImplicit false
namespace KND_Steps33
open KND_Schedule KND_Composition
def steps : List Step := [⟨"weight48",1480,1768,16⟩,⟨"weight49",1496,1768,16⟩,⟨"weight50",1512,1768,16⟩]
theorem reachable : ∀ s ∈ steps, s ∈ schedule := by decide
theorem capacity : ∀ s ∈ steps, s.len + s.size ≤ s.cap := by decide
theorem bytes (s : Step) (_reachable : s ∈ steps) (before value : State)
 (j : Nat) (bound : j<s.len+s.size) :
 model s before value j = if j<s.len then before j else value (j-s.len) :=
 byte_law s before value j bound
#print axioms reachable
#print axioms capacity
#print axioms bytes
end KND_Steps33
