import R1Z.QueryScanHistoryRealNumerics

/-! Joint impossibility of the requested whole-run event coverage, its mass
bound, and the final numerical target. This does not refute ZK_FSS. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanHistoryRealSpecificationObstruction
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.QueryScanWholeRunRepeatObstruction
  R1Z.QueryScanWholeRunRepeatReal
attribute [local instance] Classical.propDecidable

theorem small_total_implies_small_collision (κ : ℚ)
    (htotal : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ <
      1 / (2 : ℚ)^100) : κ < 1 := by
  have hκ : κ ≤ 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ :=
    le_add_of_nonneg_left (by positivity)
  have ht : 1 / (2 : ℚ)^100 < 1 := by
    apply (div_lt_one (by positivity)).2
    exact one_lt_pow₀ (by norm_num) (by decide)
  exact (hκ.trans_lt htotal).trans ht

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- For an allowed adversary, no choice of c or q can repair the whole-run
specification while satisfying the requested final target. The statement
is stronger than fixing any particular c*q^2/2^256 formula for κ. -/
theorem no_whole_run_exclusion_with_requested_total
    (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (RomFiniteBin.wire base bound))
    (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (E_coll : (fsR1P (RomFiniteBin.wire base bound) Pr 8 (by decide) P Vp).RealRand → Prop)
    (covers_repeats : ∀ r, repeatedRead (realGameP (RomFiniteBin.wire base bound) Pr 8 P Vp
      h B outputs (repeatAdversary []) x w r).observerOracle → E_coll r)
    (κ : ℚ) :
    ¬ (eventMass E_coll ≤ κ ∧
      1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ < 1 / (2 : ℚ)^100) := by
  intro hh
  exact finite_real_no_small_exclusion base bound Pr P Vp h B outputs x w E_coll
    covers_repeats κ (small_total_implies_small_collision κ hh.2) hh.1

#print axioms small_total_implies_small_collision
#print axioms no_whole_run_exclusion_with_requested_total
end R1Z.QueryScanHistoryRealSpecificationObstruction
