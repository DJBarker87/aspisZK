import R1Z.QueryScanWholeRunRepeatObstruction

/-! Specialization to the actual finite-ROM randomness and fixed observer cap.
The counterexample is unconditioned and uses the in-domain address []. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanWholeRunRepeatReal
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.QueryScanWholeRunRepeatObstruction
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The actual observer cap suffices without evaluating its numeral. -/
theorem observer_cap (base : R1Wire K CommitHandle Aux) (bound : ℕ) :
    2 ≤ (RomFiniteBin.wire base bound).qmax := by
  change 2 ≤ (2 : ℕ)^64
  exact le_self_pow₀ (by decide) (by decide)

/-- The counterexample reads are within the finite-ROM domain. -/
theorem repeat_address_in_domain (bound : ℕ) :
    ([] : List UInt8) ∈ RomFiniteBin.domain bound :=
  (RomFiniteBin.mem_domain bound []).mpr (Nat.zero_le _)

/-- No hypotheses about honest success or scan outcomes: mass is exactly one
on the finite table × eight-secret real carrier used by fsR1P. -/
theorem finite_real_repeat_mass
    (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (RomFiniteBin.wire base bound))
    (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) :
    eventMass (fun r : (fsR1P (RomFiniteBin.wire base bound) Pr 8 (by decide) P Vp).RealRand =>
      repeatedRead (realGameP (RomFiniteBin.wire base bound) Pr 8 P Vp h B outputs
        (repeatAdversary []) x w r).observerOracle) = 1 := by
  apply covering_event_mass_one
    (fun r => (realGameP (RomFiniteBin.wire base bound) Pr 8 P Vp h B outputs
      (repeatAdversary []) x w r).observerOracle)
  · intro r
    exact real_game_repeats _ _ _ _ _ _ _ _ _ _ r [] (observer_cap base bound)
  · intro _ hr
    exact hr

/-- The requested E_coll cannot simultaneously cover whole-run repeats and
have any bound κ < 1, on the retained finite-ROM experiment itself. -/
theorem finite_real_no_small_exclusion
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
    (κ : ℚ) (hκ : κ < 1) : ¬ eventMass E_coll ≤ κ := by
  exact no_small_covering_event _ E_coll
    (fun r => real_game_repeats _ _ _ _ _ _ _ _ _ _ r [] (observer_cap base bound))
    covers_repeats κ hκ

#print axioms observer_cap
#print axioms repeat_address_in_domain
#print axioms finite_real_repeat_mass
#print axioms finite_real_no_small_exclusion
end R1Z.QueryScanWholeRunRepeatReal
