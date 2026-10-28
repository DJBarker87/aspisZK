import R1Z.PV_RunJoin_FixtureRecords
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PairValidity28
open AspisPool.V7PairLeafOccupancy
/-- Occupancy validity ignores the first commitment. Establish this with
symbolic fields before instantiating any concrete note hash. -/
theorem replace_first {K : Type} [CommRing K] (pair : PairLeaf K)
    (first : Digest K) (h : pair.Valid) :
    ({pair with firstCommitment := first} : PairLeaf K).Valid := by
  rcases pair with ⟨f,o,s,iv⟩
  exact h
#print axioms replace_first
end R1Z.PV_RunJoin_PairValidity28
