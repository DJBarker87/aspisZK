import R1Z.PV_Inv_MaskRowFold
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskRowEquation
open PV_Inv_MaskRowFold PV_Inv_MaskFold

def step (block acc row : Nat) : Nat :=
  if row / 16 = block then acc ||| 2^(row % 16) else acc

/-- The explicit row loop is the filter/map/OR reference used for sort/dedup
transport. This does not assume any order for the dynamic row enumeration. -/
theorem fold_equation (block : Nat) (rows : List Nat) (initial : Nat) :
    rows.foldl (step block) initial = bits initial (rowBits block rows) := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : row / 16 = block
    · simpa [step,rowBits,bits,h] using ih (initial ||| 2^(row%16))
    · simpa [step,rowBits,bits,h] using ih initial

theorem native_set_transport (block : Nat) (xs ys : List Nat)
    (members : ∀ row, row ∈ xs ↔ row ∈ ys) :
    xs.foldl (step block) 0 = ys.foldl (step block) 0 := by
  rw [fold_equation,fold_equation]
  exact set_transport xs ys members block

#print axioms fold_equation
#print axioms native_set_transport
end R1Z.PV_Inv_MaskRowEquation
