import R1Z.PV_RunJoin_PairChecks29
import R1Z.PV_RunJoin_ForestEquality30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TwoOutputSentinel31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem source (first second : Array U32 8#usize)
    (leaf : pair_tree_profile.PoolV1PairLeafWitnessV1)
    (h : pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs first second = ok (.Ok leaf)) :
    Canon8 second ∧ second.val[7]! ≠ 0#u32 := by
  unfold pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs at h
  pv_peel h with b hb
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at h
  · cases h
  · pv_peel h with b hb
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at h
    · cases h
    · have hc := (PV_RunJoin_PortDigest29.canonical_iff second).mp hb
      rw [pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE,
        index_ok_gen second 7#usize (by decide)] at h
      simp only [bind_tc_ok] at h
      pv_peel h with zero hz
      cases zero <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · refine ⟨hc,?_⟩
        unfold aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq at hz
        simpa only [aspis_core.field.M31.ZERO,Result.ok.injEq,decide_eq_false_iff_not,UScalar.ofNatCore_val_eq] using hz
      · cases h
#print axioms source
end R1Z.PV_RunJoin_TwoOutputSentinel31
