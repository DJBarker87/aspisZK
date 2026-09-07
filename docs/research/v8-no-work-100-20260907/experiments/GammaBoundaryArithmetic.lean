/- Tiny standalone arithmetic certificate; no package imports or replay.
   This certifies the numerical boundary, not the entire cryptographic construction. -/
namespace AspisV8Research

theorem disjointRootCount :
    28 * (1048576 - 38229 : Nat) = 28289716 := by decide

theorem allRootsAreLegalBaseFieldGammas :
    (28289716 : Nat) < 2147483647 := by decide

theorem isolatedBoundaryExceedsTwoToMinus100 :
    (28289716 : Nat) * 2^100 > (2147483647 : Nat)^4 - 1 := by decide

theorem completeFibreConstructionMeetsThreshold :
    (28 * (262144 / 760) : Nat) > 9557 ∧
    (4 * 28 * (262144 / 760) : Nat) > 38229 := by decide

#print axioms disjointRootCount
#print axioms allRootsAreLegalBaseFieldGammas
#print axioms isolatedBoundaryExceedsTwoToMinus100
#print axioms completeFibreConstructionMeetsThreshold
end AspisV8Research
