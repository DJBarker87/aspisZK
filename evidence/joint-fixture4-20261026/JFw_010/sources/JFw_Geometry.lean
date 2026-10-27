import PSem_Shapes
set_option autoImplicit false
namespace AspisR1.JFw_Geometry
open OraclePortCompactDraft

def sourcePos (row : Nat) : Nat :=
  if row ≤ 2 then 32+5*row else if row ≤ 14 then 64+5*row
  else if row ≤ 25 then 155+453*(row-15) else if row = 26 then 6546 else 7015

def destPos (row : Nat) : Nat :=
  if row ≤ 2 then 32+5*row else if row ≤ 14 then 64+5*row
  else if row ≤ 25 then 171+901*(row-15) else if row = 26 then 12898 else 13831

/-- Small finite geometry table; no proof-byte evaluation. -/
theorem step (row : Nat) (bound : row < 27) :
    (rowShape row).2 ≤ 3712 ∧ (rowShape row).2 % 32 = 0 ∧
    sourcePos (row+1) = sourcePos row+5+
      (if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2) ∧
    destPos (row+1) = destPos row+5+(rowShape row).2 ∧
    sourcePos (row+1) ≤ 7015 ∧ destPos (row+1) ≤ 13831 := by
  interval_cases row <;> decide

#print axioms step
end AspisR1.JFw_Geometry
