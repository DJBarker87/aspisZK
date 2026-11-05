import NHI_Tensor
set_option autoImplicit false
namespace NHI_KindDomain
/-- Actual ordinary-kind selector from frozen weights.rs. Dense D dispatch is
outside this S2 caller statement; kind zero is never silently admitted. -/
def row (kind : Nat) : Nat := if kind<4 then kind-1 else kind-2

theorem selected (kind : Nat) (member : kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=5 ∨ kind=6) :
 row kind<5 ∧ kind<7 := by
 rcases member with rfl|rfl|rfl|rfl|rfl <;> decide

/-- The seven-part write slot and the selected five-row tensor are distinct
indices and both lie in their own bounds on every regular-kind call. -/
theorem slots : row 1=0 ∧ row 2=1 ∧ row 3=2 ∧ row 5=3 ∧ row 6=4 := by decide

#print axioms selected
#print axioms slots
end NHI_KindDomain
