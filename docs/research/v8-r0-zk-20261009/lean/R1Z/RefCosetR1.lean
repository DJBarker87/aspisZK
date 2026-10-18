import R1Z.IIPrimeR1
import R0Z.RefPayload

/-! ZF2 Claim Z (zf1/DESIGN-ZF2-SIMULATOR.txt §3.2, §5.3): on `P_R1`, the
normalised honest offset `cTilde w` of every valid, base-typed instance lies
in the public coset `refPayload x.1 B ch + range A_ch`.

The proof is `cTilde_sub_mem_range_R1` (R1Z/IIPrimeR1) with the second
instance replaced by the zero payload trace: `δ = u_w − 0` satisfies the
noise-lift hypotheses by validity of `w` alone, and the `.maskSum` patch of
`refPayload` restores `ι = 0`.  Every challenge condition is a conjunct of
`P_R1`; nothing else is assumed. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.RefCosetR1
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.Shift
  R0Z.K4 R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.NoiseLiftR1
  R0Z.IIPrimeResidual R1Z.IIPrimeR1 R0Z.RefPayload Polynomial

attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem msCell_ne (s : K) (cell : PayloadCell R1Bat) (hc : cell ≠ .maskSum) :
    msCell (Bat := R1Bat) s cell = 0 := by
  cases cell <;> first | rfl | exact absurd rfl hc

/-- Claim Z. -/
theorem cTilde_sub_ref_mem_range_R1 (h : HonestProver K) (B : PackBasis F) (hB : PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1) (ch : Challenges K)
    (hP : P_R1 h.transport B hB ch) (w : h.Instance)
    (hF : BaseTyped F (h.build w))
    (hv : R0Z.HonestValid.HonestValid x.1 B (h.build w) ch) :
    cTilde (Bat := R1Bat) h B x w ch - refPayload x.1 B ch ∈ LinearMap.range (A h.transport B ch) := by
  have hsem : ∀ i, ch.sem i ∈ K4 B hB := hP.semK4
  have hT : R0Z.K4Values.TerminalClosed (K4 B hB) x.1 B ch :=
    R0Z.TerminalClosed.terminalClosed B hB x.1 ch hsem hpub
  have hi : B.i ∈ K4 B hB := i_mem_K4 B hB
  have hu : B.u ∈ K4 B hB := u_mem_K4 B hB
  obtain ⟨u, hu_def⟩ : ∃ u, u = R0Z.PayloadSplit.actual x.1 B (h.build w) ch 0 := ⟨_, rfl⟩
  have hu4 : ∀ c r, u c r ∈ K4 B hB := fun c r => by
    rw [hu_def]; exact R0Z.K4Values.actual_mem B hB x.1 _ ch hF (hsem 0) (hsem 1) 0 c r
  -- Step N, with δ = u − 0
  have hδ : ∀ c : Fin 16, u (Fin.castLE (by omega) c) ∈ Wsem (K := K) (F := F) := by
    intro c
    rw [hu_def, mem_Wsem_iff]
    refine ⟨fun r => mem_baseF (R0Z.IIPrimeResidual.actual_sem_mem x.1 B _ ch hF
      (Fin.castLE (by omega) c) c.isLt r), ?_⟩
    have hne : (Fin.castLE (by omega) c : Fin 29).val ≠ 26 := by
      have := c.isLt
      simp only [Fin.val_castLE]
      omega
    exact R0Z.HonestValid.actual_inactive_sum _ _ _ _ _ hne
  have hδ26 : u 26 ∈ Wh1 B hB := by
    rw [hu_def, mem_Wh1_iff]
    exact ⟨fun r => R0Z.K4Values.actual_mem B hB x.1 _ ch hF (hsem 0) (hsem 1) 0 26 r, hv.2.2⟩
  obtain ⟨n, hn1, hn2⟩ := noise_lift_R1 h.transport B hB ch hP u hδ hδ26
  obtain ⟨τ, hτ_def⟩ : ∃ τ, τ = u - R0Z.JointTrace.tapeLinear B (inrN n) := ⟨_, rfl⟩
  have hAn : A (Bat := R1Bat) h.transport B ch (inrN n) =
      R0Z.PayloadSplit.L h.transport B ch (R0Z.JointTrace.tapeLinear B (inrN n)) := rfl
  have hLτ : R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ =
      R0Z.PayloadSplit.L h.transport B ch u - A h.transport B ch (inrN n) := by
    rw [hτ_def, map_sub, hAn]
  have hown : ∀ l : Fin 29,
      ownRead (Bat := R1Bat) (F := F) l (R0Z.PayloadSplit.L h.transport B ch τ) = 0 := by
    intro l
    rw [hLτ, map_sub (ownRead (Bat := R1Bat) (F := F) l)]
    by_cases hl : l.val < 16 ∨ l.val = 26
    · rw [hn1 l hl, sub_self]
    · have hz : u l = 0 := by
        rw [hu_def]
        exact actual_other_zero _ _ _ _ l hl
      rw [hn2 l hl, own_L_eq_obs, hz, map_zero, sub_zero]
  have hcl : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ (.pointClaim j c) = 0 := by
    intro j c
    simpa only [ownRead, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun (hown c) (.claim j)
  have hex : ∀ c, R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ (.extraClaim c) = 0 := by
    intro c
    simpa only [ownRead, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun (hown c) .extra
  have hoo : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ (.ood j c) = 0 := by
    intro j c
    simpa only [ownRead, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun (hown c) (.ood j)
  have hop : ∀ q s c, R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ (.opened q s c) = 0 := by
    intro q s c
    simpa only [ownRead, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun (hown c) (.opened q s)
  -- the residual
  obtain ⟨Y, hY_def⟩ : ∃ Y : Payload K R1Bat,
      Y = cTilde (Bat := R1Bat) h B x w ch - refPayload x.1 B ch - A h.transport B ch (inrN n) :=
    ⟨_, rfl⟩
  have hY : Y = R0Z.PayloadSplit.L h.transport B ch τ +
      (R0Z.PayloadSplit.roundInclusion (Bat := R1Bat) (R0Z.PayloadSplit.originalRounds x.1 B ch u) -
        R0Z.PayloadSplit.roundInclusion (R0Z.PayloadSplit.originalRounds x.1 B ch 0) -
        (kOf h B x w ch - k0 x.1 B ch) • dir) - msCell (S0 x.1 B ch) := by
    rw [hY_def, cTilde_eq, refPayload, hLτ, ← hu_def, sub_smul]
    abel
  have hYcell : ∀ cell : PayloadCell R1Bat, (∀ j i, cell ≠ .semanticCoeff j i) →
      cell ≠ .maskSum → Y cell = R0Z.PayloadSplit.L h.transport B ch τ cell := by
    intro cell hc hm
    rw [hY, Pi.sub_apply, Pi.add_apply, roundOnly_cell _ _ _ cell hc, msCell_ne _ cell hm,
      add_zero, sub_zero]
  have hYcl : ∀ j c, Y (.pointClaim j c) = 0 := fun j c => by
    rw [hYcell (.pointClaim j c) (by intro _ _ hc; cases hc) (by intro hc; cases hc)]; exact hcl j c
  have hYex : ∀ c, Y (.extraClaim c) = 0 := fun c => by
    rw [hYcell (.extraClaim c) (by intro _ _ hc; cases hc) (by intro hc; cases hc)]; exact hex c
  have hYoo : ∀ j c, Y (.ood j c) = 0 := fun j c => by
    rw [hYcell (.ood j c) (by intro _ _ hc; cases hc) (by intro hc; cases hc)]; exact hoo j c
  have hYop : ∀ q s c, Y (.opened q s c) = 0 := fun q s c => by
    rw [hYcell (.opened q s c) (by intro _ _ hc; cases hc) (by intro hc; cases hc)]; exact hop q s c
  have hYia : Y .inactiveSum = 0 := by
    rw [hY_def, Pi.sub_apply, Pi.sub_apply, R0Z.HonestValid.inactive_cTilde_zero h B x w ch hv,
      inactive_refPayload, R0Z.HonestValid.inactive_A, sub_zero, sub_zero]
  have hYiota : R0Z.HonestValid.iota Y = 0 := by
    rw [hY_def, map_sub, map_sub, R0Z.HonestValid.iota_cTilde_zero h B x w ch hv, iota_refPayload,
      R0Z.HonestValid.iota_A, sub_zero, sub_zero]
  have hLia : R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ .inactiveSum = 0 := by
    rw [← hYcell .inactiveSum (by intro _ _ hc; cases hc) (by intro hc; cases hc)]
    exact hYia
  -- batched cells in B0R1′
  have hYb : R0Z.SilentReduction.batRead (F := F) Y ∈ B0R1' (F := F) h.transport ch := by
    have e : R0Z.SilentReduction.batRead (F := F) Y =
        R0Z.SilentReduction.batRead (F := F) (R0Z.PayloadSplit.L (Bat := R1Bat) h.transport B ch τ) := by
      funext b
      rw [batRead_apply, batRead_apply]
      exact hYcell (.bat b) (by intro _ _ hc; cases hc) (by intro hc; cases hc)
    rw [e]
    refine Submodule.mem_inf.2 ⟨bat_L_mem_B0R1 h.transport B ch τ hcl hex hoo hop hLia, ?_⟩
    intro p hp
    rw [batRead_apply]
    exact folded_unqueried_zero h.transport ch τ p hp
  -- the round part
  have hYchain : Y ∈ ChainEqs (Bat := R1Bat) ch := by
    rw [hY_def]
    exact (ChainEqs (Bat := R1Bat) ch).sub_mem ((ChainEqs (Bat := R1Bat) ch).sub_mem
      (cTilde_mem_chainEqs h B x w ch) (refPayload_mem_chainEqs x.1 B ch))
      (A_mem_chainEqs h.transport B ch _)
  have hYphi : Phi0 B ch Y = 0 := by
    rw [hY_def, map_sub, map_sub, Phi0_cTilde h B x w ch hP.halfOK,
      Phi0_refPayload x.1 B ch hP.halfOK, Phi0_A, sub_zero, sub_zero]
  have hYmask : claimMask B (alpha ch) Y = 0 := by
    simp only [claimMask, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      proj_apply, hYcl, hYex, smul_zero, Finset.sum_const_zero, add_zero]
  have hY9 : (R0Z.Chain.roundPoly 9 Y).eval (alpha ch 9) = 0 := by
    have e : evalRound9 ch Y = Phi0 B ch Y + claimMask B (alpha ch) Y := by
      simp only [Phi0, LinearMap.sub_apply, sub_add_cancel]
    rw [hYphi, hYmask, add_zero] at e
    rw [R0Z.Chain.roundPoly_nine]
    exact e
  have hτ4 : ∀ c r, τ c r ∈ K4 B hB := by
    intro c r
    have htape : R0Z.JointTrace.tapeLinear B (inrN n) c r =
        R0Z.PayloadSplit.actual x.1 B (h.build w) ch (inrN n) c r -
          R0Z.PayloadSplit.actual x.1 B (h.build w) ch 0 c r := by
      rw [R0Z.JointTrace.actual_affine x.1 B (h.build w) ch (inrN n), Pi.add_apply, Pi.add_apply,
        add_sub_cancel_left]
    rw [hτ_def]
    simp only [Pi.sub_apply]
    rw [htape]
    exact (K4 B hB).sub_mem (hu4 c r)
      ((K4 B hB).sub_mem
        (R0Z.K4Values.actual_mem B hB x.1 _ ch hF (hsem 0) (hsem 1) _ c r)
        (R0Z.K4Values.actual_mem B hB x.1 _ ch hF (hsem 0) (hsem 1) 0 c r))
  have hk4 : kOf h B x w ch ∈ K4 B hB := by
    have ha : ∀ i, alpha ch i ∈ K4 B hB := R0Z.K4Values.alpha_mem _ ch hsem
    unfold kOf fOrig
    refine (K4 B hB).mul_mem ((K4 B hB).mul_mem (hsem 14) (hT _ _ (fun j c =>
      R0Z.K4Values.honestClaims_mem _ _ (fun c r => R0Z.K4Values.actual_mem B hB x.1 _ ch hF
        (hsem 0) (hsem 1) 0 c r) _ ha j c) ha)) ?_
    exact (K4 B hB).inv_mem ((K4 B hB).sub_mem (ha 9) (half_mem_K4 B hB))
  have hYK4 : ∀ j i, Y (.semanticCoeff j i) ∈ K4 B hB := by
    intro j i
    rw [hY, Pi.sub_apply, Pi.add_apply, msCell_semanticCoeff, sub_zero]
    refine (K4 B hB).add_mem (L_round_mem _ h.transport B hi hu ch hsem τ hτ4 j i) ?_
    show R0Z.PayloadSplit.originalRounds x.1 B ch u j i -
        R0Z.PayloadSplit.originalRounds x.1 B ch 0 j i -
        (kOf h B x w ch - k0 x.1 B ch) * (if j = 9 then (X - C (1 / 2 : K)).coeff i.val else 0)
      ∈ K4 B hB
    exact (K4 B hB).sub_mem ((K4 B hB).sub_mem
      (R0Z.K4Values.originalRounds_mem _ x.1 B ch hsem hT u hu4 j i)
      (R0Z.K4Values.originalRounds_mem _ x.1 B ch hsem hT 0 (fun _ _ => (K4 B hB).zero_mem) j i))
      ((K4 B hB).mul_mem ((K4 B hB).sub_mem hk4 (k0_mem B hB x.1 ch hsem hT))
        (R0Z.K4Values.dirCoeff_mem B hB j i))
  have hYT : R0Z.Z4Maps.roundProjection (F := F) Y ∈
      R0Z.SilentReduction.ChainT0K4 (Bat := R1Bat) B hB ch := by
    refine Submodule.mem_inf.2 ⟨?_, (R0Z.SilentReduction.mem_K4Round_iff B hB _).2 hYK4⟩
    rw [Submodule.restrictScalars_mem]
    exact roundProjection_mem_chainT0 ch Y hYchain hY9
  -- Step M
  obtain ⟨m, hm⟩ := mask_lift_of h.transport B hB ch (B0R1' h.transport ch) hP.qprime
    (bat_ker_own_le_B0R1' h.transport B ch) hP.breach Y hYcl hYex hYoo hYop hYia hYiota hYT hYb
  refine ⟨inlM m + inrN n, ?_⟩
  rw [map_add, ← LinearMap.comp_apply (A (Bat := R1Bat) h.transport B ch) inlM m, hm, hY_def,
    sub_add_cancel]

#print axioms msCell_ne
#print axioms cTilde_sub_ref_mem_range_R1
end R1Z.RefCosetR1
