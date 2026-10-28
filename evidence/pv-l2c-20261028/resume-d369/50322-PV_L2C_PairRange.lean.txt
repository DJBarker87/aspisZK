import R1Z.PV_RunJoin_PairChecks29
set_option autoImplicit false
namespace PV_L2C_PairRange
open Aeneas Aeneas.Std Result R1Z R1Z.BuilderForestAdmissionPort

/-- The source validates both raw occupancy coordinates before using their
field equations. This includes the inverse, not only commitment digests. -/
theorem coordinates (p : pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (h : p.validate = ok (.Ok ())) :
    p.second_occupied.val < 2147483647 ∧
    p.second_occupancy_inverse.val < 2147483647 := by
  unfold pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate at h
  pv_peel h with first hf
  cases first <;> simp only [Bool.false_eq_true,↓reduceIte] at h
  · cases h
  · pv_peel h with second hs
    cases second <;> simp only [Bool.false_eq_true,↓reduceIte] at h
    · cases h
    · split at h
      · cases h
      · rename_i ho
        split at h
        · cases h
        · rename_i hi
          have ho' : ¬ 2147483647 ≤ p.second_occupied.val := by
            simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq] using ho
          have hi' : ¬ 2147483647 ≤ p.second_occupancy_inverse.val := by
            simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq] using hi
          exact ⟨by omega,by omega⟩
#print axioms coordinates
end PV_L2C_PairRange
