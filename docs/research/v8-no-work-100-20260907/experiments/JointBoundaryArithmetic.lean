/- Standalone finite arithmetic only; no generated recurrence or field theorem. -/
namespace AspisV8ResearchJoint
theorem jointCount : 28 * (262144-9557 : Nat) = 7072436 := by decide
theorem legalRoots : (7072436 : Nat) < 2147483647 := by decide
theorem bothGates : (4*9558 : Nat) > 38229 ∧ (9558 : Nat) > 9557 := by decide
theorem commonRootsForceZero : (4*9557 : Nat) > 1024 := by decide
theorem disproves2800 : (7072436 : Nat) > 2800 := by decide
theorem exceeds104BitEvent :
    (7072436 : Nat)*2^104 > (2147483647 : Nat)^4-1 := by decide
theorem below101BitEvent :
    (7072436 : Nat)*2^101 < (2147483647 : Nat)^4-1 := by decide
-- The analytic seventh-power argument is in the report. Certify only its
-- small field-size input here, avoiding reduction of the unnecessary 2^700.
theorem deepFieldSizeBelow124Bits :
    (2147483647 : Nat)^4 < 2^124 := by decide
#print axioms jointCount
#print axioms legalRoots
#print axioms bothGates
#print axioms commonRootsForceZero
#print axioms disproves2800
#print axioms exceeds104BitEvent
#print axioms below101BitEvent
#print axioms deepFieldSizeBelow124Bits
end AspisV8ResearchJoint
