import R0Z.HonestValid
import R0Z.K4Values

/-! J15 (DESIGN-ii-prime §2.3–2.4; DESIGN-R1-PRIVACY-MODEL §4 J15-R1), the
Bat-generic part: the residual steps and the mask lift of clause (ii′).

* `laneOf_actual_zero` (row-1023 lemma for J0b, LOG D36.4): the production
  lanes of the payload trace `actual pub B t ch 0` are those of the prepared
  instance `prepare pub t ch`; the row-1023 rebalancing and the zero affine
  tape change no lane (TerminalEligible.lanes_eligible, openings_applyAff).
* Lane facts of the payload trace: F-valued semantic lanes, zero lanes
  16..25, 27, 28.
* `cTilde_eq`, `Phi0_cTilde` (R4): `cTilde = L u + O u − k • dir` with
  `k = fOrig u(α)·(α₉ − ½)⁻¹`, and `Φ₀(cTilde) = 0` when `α₉ ≠ ½`.
* `ChainEqs` (R6): the nine boundary-chain equalities as a K-submodule; it
  contains every `L τ`, every original-round inclusion, `dir`, all of `A`
  and every `cTilde`.  `roundProjection_mem_chainT0` turns it, with the
  terminal equation, into `ChainT0`.
* `maskLinear_mem`, `L_round_mem` (R7): the round cells of `L τ` lie in any
  subfield containing `B.i`, `B.u`, the challenges and the trace values.
* `mask_lift_of` (§2.4, generic linear algebra): a payload with zero own and
  inactive cells, zero initial-sum defect, `Chain_T0₄` round part and batched
  part in a subspace `B0` is a mask-tape image, given (Q′), `bat(ker own) ≤ B0`
  and `B0 ≤ bat(ker own ⊓ ker R)` (BReach).

No conjunct of any challenge predicate is asserted here. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.IIPrimeResidual
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView
  R0Z.Partition R0Z.D12 R0Z.Shift R0Z.K4 Polynomial

attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ### Lanes of the payload trace -/

/-- Row-1023 lemma (LOG D36.4): the lanes of the payload trace equal those of
the prepared instance, for every `λ, χ`.  Row 1023 is read by `rowOpenings`
(at rows 1023, 1022 and 1011), but no lane value changes under the
rebalancing (`lanes_eligible`; copy endpoints are `Protected`, row ≠ 1023). -/
theorem laneOf_actual_zero (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (lam chi : K) :
    laneOf (PayloadSplit.actual pub B t ch 0) pub lam chi B = laneOf (prepare pub t ch) pub lam chi B := by
  have h0 : (Sum.elim 0 (aff (0 : T K F)) : MaskTape K F) = 0 := by
    rw [map_zero (aff (K := K) (F := F))]
    funext z
    cases z <;> rfl
  funext i bits
  rw [laneOf_eq_laneAt, laneOf_eq_laneAt]
  unfold PayloadSplit.actual
  rw [R0Z.TerminalEligible.openings_applyAff, R0Z.TerminalEligible.h1_applyAff, h0,
    R0Z.TerminalEligible.h1Padding_zero, Pi.zero_apply, add_zero,
    R0Z.TerminalEligible.prepare_eligible, R0Z.TerminalEligible.lanes_eligible]

/-- The semantic lanes of the payload trace of a base-typed instance are F-valued. -/
theorem actual_sem_mem (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (hF : BaseTyped F t) (l : Fin 29) (hl : l.val < 16) (s : Fin 1024) :
    PayloadSplit.actual pub B t ch 0 l s ∈ F := by
  unfold PayloadSplit.actual applyAff
  try dsimp only
  rw [if_pos hl]
  unfold prepare
  try dsimp only
  rw [if_neg (by omega)]
  unfold applyEligible
  try dsimp only
  rw [if_pos hl]
  refine R0Z.K4Values.balance_mem F 1023 _ (fun s' => ?_) s
  refine F.add_mem (hF l (by omega) s') ?_
  unfold semanticNoise
  split_ifs
  · exact Subtype.mem _
  · exact F.zero_mem

/-- Lanes 16..25, 27, 28 of the payload trace are zero. -/
theorem actual_other_zero (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (l : Fin 29) (hl : ¬ (l.val < 16 ∨ l.val = 26)) :
    PayloadSplit.actual pub B t ch 0 l = 0 := by
  have he : PayloadSplit.actual pub B t ch 0 =
      traceBase (prepare pub (applyEligible t (0 : T K F).2.2) ch) + traceLinear B (aff (0 : T K F)) :=
    applyAff_eq_base_add B (prepare pub (applyEligible t (0 : T K F).2.2) ch) (aff (0 : T K F))
  rw [he, map_zero (aff (K := K) (F := F)), map_zero (traceLinear B), add_zero]
  funext s
  simp only [traceBase, hl, ↓reduceIte, Pi.zero_apply]

/-! ### `cTilde` and Φ₀ (R4) -/

/-- The direction coefficient `k = fOrig u(α)·(α₉ − ½)⁻¹`. -/
def kOf (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) : K :=
  fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) (alpha ch) * (alpha ch 9 - 1/2)⁻¹

theorem cTilde_eq (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    cTilde (Bat := Bat) h B x w ch =
      PayloadSplit.L h.transport B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) +
        PayloadSplit.roundInclusion
          (PayloadSplit.originalRounds x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0)) -
        kOf h B x w ch • dir := by
  unfold cTilde kOf
  rw [originalOf_c]
  rw [show (c (Bat := Bat) h B x w ch) = _ from R0Z.HonestValid.c_eq h B x w ch]
  all_goals rfl

/-- (R4): `Φ₀(cTilde) = 0` off `α₉ = ½`. -/
theorem Phi0_cTilde (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (hhalf : alpha ch 9 ≠ 1/2) :
    Phi0 B ch (cTilde (Bat := Bat) h B x w ch) = 0 := by
  rw [cTilde_eq, map_sub, map_add, Phi0_L, Phi0_roundInclusion, evalRound9_originalRounds,
    map_smul, Phi0_dir, smul_eq_mul, zero_add]
  unfold kOf
  have hne : alpha ch 9 - 1/2 ≠ 0 := sub_ne_zero.mpr hhalf
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, sub_self]

/-! ### The chain equalities (R6) -/

/-- The nine boundary-chain equalities of the ten rounds. -/
def ChainEqs (ch : Challenges K) : Submodule K (Payload K Bat) :=
  ⨅ j : Fin 9, LinearMap.ker
    (Chain.evalRound j.succ 0 + Chain.evalRound j.succ 1 - Chain.evalRound j.castSucc (alpha ch j.castSucc))

theorem mem_chainEqs_iff (ch : Challenges K) (v : Payload K Bat) :
    v ∈ ChainEqs ch ↔ ∀ j : Fin 9, (Chain.roundPoly j.succ v).eval 0 + (Chain.roundPoly j.succ v).eval 1 =
      (Chain.roundPoly j.castSucc v).eval (alpha ch j.castSucc) := by
  simp only [ChainEqs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.add_apply,
    LinearMap.sub_apply, Chain.evalRound_apply, sub_eq_zero]

theorem initialChain0_le (ch : Challenges K) :
    Chain.InitialChain0 (Bat := Bat) ch ≤ ChainEqs ch := inf_le_right

theorem L_mem_chainEqs (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (τ : Trace K) :
    PayloadSplit.L (Bat := Bat) π B ch τ ∈ ChainEqs ch := by
  rw [mem_chainEqs_iff]
  intro j
  rw [PureRounds.roundPoly_L, PureRounds.roundPoly_L]
  exact Chain.rounds_chain ch _ (maskLinear_vdeg π B τ) j

theorem originalRounds_mem_chainEqs (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K) :
    PayloadSplit.roundInclusion (Bat := Bat) (PayloadSplit.originalRounds pub B ch t) ∈ ChainEqs ch := by
  rw [mem_chainEqs_iff]
  intro j
  rw [Chain.roundPoly_originalRounds, Chain.roundPoly_originalRounds]
  exact Chain.rounds_chain ch _ (vdeg_fOrig pub B ch t) j

theorem dir_mem_chainEqs (ch : Challenges K) : (dir : Payload K Bat) ∈ ChainEqs ch :=
  initialChain0_le ch (Chain.dir_mem_initialChain0 ch)

theorem A_mem_chainEqs (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (t : T K F) :
    A (Bat := Bat) π B ch t ∈ ChainEqs ch := by
  have hA : A (Bat := Bat) π B ch t = PayloadSplit.L π B ch (JointTrace.tapeLinear B t) := rfl
  rw [hA]
  exact L_mem_chainEqs π B ch _

theorem cTilde_mem_chainEqs (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    cTilde (Bat := Bat) h B x w ch ∈ ChainEqs ch := by
  rw [cTilde_eq]
  exact (ChainEqs ch).sub_mem
    ((ChainEqs ch).add_mem (L_mem_chainEqs _ B ch _) (originalRounds_mem_chainEqs x.1 B ch _))
    ((ChainEqs ch).smul_mem _ (dir_mem_chainEqs ch))

theorem roundPoly_roundProjection (v : Payload K Bat) (j : Fin 10) :
    Chain.roundPoly j (PayloadSplit.roundInclusion (Bat := Bat)
      (R0Z.Z4Maps.roundProjection (F := F) v)) = Chain.roundPoly j v :=
  (Chain.roundPoly_roundInclusion j _).trans (Chain.roundPoly_apply j v).symm

/-- The chain equalities and the terminal equation give `ChainT0`. -/
theorem roundProjection_mem_chainT0 (ch : Challenges K) (v : Payload K Bat) (hv : v ∈ ChainEqs ch)
    (h9 : (Chain.roundPoly 9 v).eval (alpha ch 9) = 0) :
    R0Z.Z4Maps.roundProjection (F := F) v ∈ R0Z.SilentReduction.ChainT0 (Bat := Bat) ch := by
  rw [R0Z.SilentReduction.mem_chainT0_iff]
  simp only [roundPoly_roundProjection]
  exact ⟨(mem_chainEqs_iff ch v).1 hv, h9⟩

/-! ### Round cells in a subfield (R7) -/

theorem maskLinear_mem (S : Subfield K) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (hi : B.i ∈ S) (hu : B.u ∈ S) (a : Fin 10 → K) (ha : ∀ i, a i ∈ S) (τ : Trace K)
    (hτ : ∀ c r, τ c r ∈ S) : PayloadSplit.maskLinear π B a τ ∈ S := by
  rw [PayloadSplit.maskLinear_apply]
  have hcl := fun j c => R0Z.K4Values.honestClaims_mem S τ hτ a ha j c
  have hml : ∀ fam : ℕ, R0P.Mask.maskLinear fam a ∈ S :=
    fun fam => sum_mem fun j _ => S.mul_mem (natCast_mem S _) (ha j)
  have htb : ∀ j, R0P.Mask.towerBasis B j ∈ S := by
    intro j
    unfold R0P.Mask.towerBasis
    split_ifs
    · exact S.one_mem
    · exact hi
    · exact hu
    · exact S.mul_mem hi hu
  refine S.add_mem ?_ ?_
  · unfold R0P.Mask.maskValue
    refine S.add_mem (S.add_mem (sum_mem fun c _ => S.mul_mem ?_ (hcl _ _))
      (S.mul_mem ?_ (hcl _ _))) (sum_mem fun c _ => S.mul_mem ?_ (hcl _ _))
    · show R0P.Mask.mulTowerBasis B _ _ ∈ S
      exact S.mul_mem (htb _) (S.pow_mem (hml 0) _)
    · show 1 + R0P.Mask.maskLinear 16 a ^ 26 ∈ S
      exact S.add_mem S.one_mem (S.pow_mem (hml 16) _)
    · show R0P.Mask.mulTowerBasis B _ _ ∈ S
      exact S.mul_mem (htb _) (S.pow_mem (hml 0) _)
  · unfold R0P.Mask.honestExtra AspisR0.RoundNormalization.dot
    refine sum_mem fun j _ => S.mul_mem ?_ ?_
    · unfold R0P.Mask.libraWeight R0P.SemSource.libraWeight
      split_ifs
      · exact S.pow_mem (ha 8) _
      · exact S.pow_mem (ha 9) _
      · exact S.zero_mem
    · unfold coeffsOf
      exact hτ _ _

theorem L_round_mem (S : Subfield K) (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (hi : B.i ∈ S) (hu : B.u ∈ S) (ch : Challenges K) (hsem : ∀ i, ch.sem i ∈ S)
    (τ : Trace K) (hτ : ∀ c r, τ c r ∈ S) (j : Fin 10) (i : Fin 28) :
    PayloadSplit.L (Bat := Bat) π B ch τ (.semanticCoeff j i) ∈ S := by
  rw [PayloadSplit.L_round, PayloadSplit.rounds_apply]
  exact R0Z.K4Values.interpolate_coeff_mem S _ (fun k => sum_mem fun tail _ =>
    maskLinear_mem S π B hi hu _ (R0Z.K4Values.roundPoint_mem S ch hsem j k.val tail) τ hτ) i.val

/-! ### Round-only payloads -/

/-- A difference of round inclusions and a multiple of `dir` vanishes off the
round cells. -/
theorem roundOnly_cell (p p' : PayloadSplit.RoundPayload K) (k : K) (cell : PayloadCell Bat)
    (hc : ∀ j i, cell ≠ .semanticCoeff j i) :
    (PayloadSplit.roundInclusion (Bat := Bat) p - PayloadSplit.roundInclusion p' - k • dir :
      Payload K Bat) cell = 0 := by
  cases cell with
  | semanticCoeff j i => exact absurd rfl (hc j i)
  | maskSum => show (0 : K) - 0 - k * 0 = 0; ring
  | pointClaim j c => show (0 : K) - 0 - k * 0 = 0; ring
  | extraClaim c => show (0 : K) - 0 - k * 0 = 0; ring
  | ood j c => show (0 : K) - 0 - k * 0 = 0; ring
  | inactiveSum => show (0 : K) - 0 - k * 0 = 0; ring
  | opened q s c => show (0 : K) - 0 - k * 0 = 0; ring
  | bat b => show (0 : K) - 0 - k * 0 = 0; ring

/-! ### The mask lift (DESIGN-ii-prime §2.4) -/

theorem nonRound_pointClaim (v : Payload K Bat) (j : Fin 3) (c : Fin 29) :
    nonRound (F := F) v (.pointClaim j c) = v (.pointClaim j c) := rfl

theorem nonRound_inactiveSum (v : Payload K Bat) :
    nonRound (F := F) v .inactiveSum = v .inactiveSum := rfl

theorem nonRound_extraClaim (v : Payload K Bat) (c : Fin 29) :
    nonRound (F := F) v (.extraClaim c) = v (.extraClaim c) := rfl

/-- `mask_lift`, generic in the batched block and in the relation space `B0`. -/
theorem mask_lift_of (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (B0 : Submodule F (Bat → K))
    (hQ : R0Z.SilentReduction.QPrime (Bat := Bat) π B hB ch)
    (hown : (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch)).map
      (R0Z.SilentReduction.batMap (Bat := Bat) π B ch) ≤ B0)
    (hR : B0 ≤ (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch) ⊓
      LinearMap.ker (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch)).map
        (R0Z.SilentReduction.batMap (Bat := Bat) π B ch))
    (Y : Payload K Bat)
    (hclaim : ∀ j c, Y (.pointClaim j c) = 0) (hextra : ∀ c, Y (.extraClaim c) = 0)
    (hood : ∀ j c, Y (.ood j c) = 0) (hopen : ∀ q s c, Y (.opened q s c) = 0)
    (hia : Y .inactiveSum = 0) (hinit : R0Z.HonestValid.iota Y = 0)
    (hT : R0Z.Z4Maps.roundProjection (F := F) Y ∈ R0Z.SilentReduction.ChainT0K4 (Bat := Bat) B hB ch)
    (hb : R0Z.SilentReduction.batRead (F := F) Y ∈ B0) :
    Y ∈ LinearMap.range ((A (Bat := Bat) π B ch).comp inlM) := by
  obtain ⟨x0, hx0, hRx0⟩ := Submodule.mem_map.1 (hQ hT)
  have hbx0 : R0Z.SilentReduction.batMap (Bat := Bat) π B ch x0 ∈ B0 :=
    hown (Submodule.mem_map_of_mem hx0)
  obtain ⟨y, hy, hby⟩ := Submodule.mem_map.1 (hR (B0.sub_mem hb hbx0))
  obtain ⟨hyo, hyR⟩ := Submodule.mem_inf.1 hy
  have hown_m : R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (x0 + y) = 0 := by
    rw [map_add, LinearMap.mem_ker.1 hx0, LinearMap.mem_ker.1 hyo, add_zero]
  have hR_m : R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (x0 + y) =
      R0Z.Z4Maps.roundProjection (F := F) Y := by
    rw [map_add, hRx0, LinearMap.mem_ker.1 hyR, add_zero]
  have hbat_m : R0Z.SilentReduction.batMap (Bat := Bat) π B ch (x0 + y) =
      R0Z.SilentReduction.batRead (F := F) Y := by
    rw [map_add, hby]
    abel
  have hproj : R0Z.Z4Maps.roundProjection (F := F) ((A (Bat := Bat) π B ch).comp inlM (x0 + y)) =
      R0Z.Z4Maps.roundProjection (F := F) Y := hR_m
  refine ⟨x0 + y, ?_⟩
  apply R0Z.SilentReduction.payload_ext (F := F)
  · funext cell
    cases cell with
    | semanticCoeff j i => rfl
    | maskSum =>
      show (A (Bat := Bat) π B ch).comp inlM (x0 + y) .maskSum = Y .maskSum
      rw [R0Z.SilentReduction.ms_pure_eq_initial,
        R0Z.SilentReduction.roundPoly_eq_of_roundProjection hproj 0]
      have hi := hinit
      rw [R0Z.HonestValid.iota_apply] at hi
      exact sub_eq_zero.mp hi
    | pointClaim j c =>
      have h1 : (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.pointClaim j c) = 0 := by
        simpa only [R0Z.SilentReduction.ownMap, R0Z.SilentReduction.ownProj, LinearMap.comp_apply,
          LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown_m (.pointClaim j c)
      rw [nonRound_pointClaim, nonRound_pointClaim, h1, hclaim j c]
    | extraClaim c =>
      have h1 : (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.extraClaim c) = 0 := by
        simpa only [R0Z.SilentReduction.ownMap, R0Z.SilentReduction.ownProj, LinearMap.comp_apply,
          LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown_m (.extraClaim c)
      rw [nonRound_extraClaim, nonRound_extraClaim, h1, hextra c]
    | ood j c =>
      have h1 : (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.ood j c) = 0 := by
        simpa only [R0Z.SilentReduction.ownMap, R0Z.SilentReduction.ownProj, LinearMap.comp_apply,
          LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown_m (.ood j c)
      show (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.ood j c) = Y (.ood j c)
      rw [h1, hood j c]
    | inactiveSum =>
      rw [nonRound_inactiveSum, nonRound_inactiveSum,
        R0Z.SilentReduction.ia_pure_zero (Bat := Bat) π B ch (x0 + y), hia]
    | opened q s c =>
      have h1 : (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.opened q s c) = 0 := by
        simpa only [R0Z.SilentReduction.ownMap, R0Z.SilentReduction.ownProj, LinearMap.comp_apply,
          LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown_m (.opened q s c)
      show (A (Bat := Bat) π B ch).comp inlM (x0 + y) (.opened q s c) = Y (.opened q s c)
      rw [h1, hopen q s c]
    | bat b =>
      exact congrFun hbat_m b
  · exact hproj

#print axioms laneOf_actual_zero
#print axioms actual_sem_mem
#print axioms actual_other_zero
#print axioms kOf
#print axioms cTilde_eq
#print axioms Phi0_cTilde
#print axioms mem_chainEqs_iff
#print axioms initialChain0_le
#print axioms L_mem_chainEqs
#print axioms originalRounds_mem_chainEqs
#print axioms dir_mem_chainEqs
#print axioms A_mem_chainEqs
#print axioms cTilde_mem_chainEqs
#print axioms roundPoly_roundProjection
#print axioms roundProjection_mem_chainT0
#print axioms maskLinear_mem
#print axioms L_round_mem
#print axioms roundOnly_cell
#print axioms nonRound_pointClaim
#print axioms nonRound_extraClaim
#print axioms nonRound_inactiveSum
#print axioms mask_lift_of
end R0Z.IIPrimeResidual
