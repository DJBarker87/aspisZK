import R0Z.IIPrimeResidual

/-! ZF2 (zf1/DESIGN-ZF2-SIMULATOR.txt §3.2, §5.1): the public reference
payload and the explicit simulator, generic in the batched layer.

* `refPayload pub B ch`: `cTilde`'s formula (`cTilde_eq`) at the zero payload
  trace (`L 0 = 0`), plus `S₀ = Σ_b fOrig(0)(b)` in the `.maskSum` cell.  It is
  a function of `(pub, B, ch)` only.
* Its silent values: `ι = 0`, `.inactiveSum = 0`, `Φ₀ = 0` (α₉ ≠ ½), the chain
  equalities, round cells in `K₄` (under `TerminalClosed`), zero on every cell
  other than the round cells and `.maskSum`.
* `simE π B outputs x ch t = (metadata, Ψ_ch (refPayload + A_ch (equiv⁻¹ t)))`:
  no instance, no choice.
* `equalLaws_simE_of`: given clause (i′) for `w` and
  `cTilde w − refPayload ∈ range A_ch`, the honest view of `w` at `ch` and
  `simE … ch` have equal laws (the proof of `hvzk_on_of` with the chosen
  witness replaced by `refPayload`).

No challenge predicate is asserted here. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.RefPayload
open R0P R0P.Sumcheck R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
  R0Z.Shift R0Z.K4 Polynomial

attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ### The reference payload -/

/-- The payload with `s` at `.maskSum` and `0` elsewhere. -/
def msCell (s : K) : Payload K Bat := fun cell => match cell with
  | .maskSum => s
  | _ => 0

theorem msCell_maskSum (s : K) : msCell (Bat := Bat) s .maskSum = s := rfl
theorem msCell_semanticCoeff (s : K) (j : Fin 10) (i : Fin 28) :
    msCell (Bat := Bat) s (.semanticCoeff j i) = 0 := rfl
theorem msCell_pointClaim (s : K) (j : Fin 3) (c : Fin 29) :
    msCell (Bat := Bat) s (.pointClaim j c) = 0 := rfl
theorem msCell_extraClaim (s : K) (c : Fin 29) : msCell (Bat := Bat) s (.extraClaim c) = 0 := rfl

/-- The direction coefficient of the zero payload trace. -/
def k0 (pub : Public K) (B : PackBasis F) (ch : Challenges K) : K :=
  fOrig pub B ch 0 (alpha ch) * (alpha ch 9 - 1/2)⁻¹

/-- The Boolean sum of the original terminal at the zero payload trace. -/
def S0 (pub : Public K) (B : PackBasis F) (ch : Challenges K) : K :=
  bsumB 10 (fun b => fOrig pub B ch 0 (ofBool b))

/-- The public reference payload (design §3.2). -/
def refPayload (pub : Public K) (B : PackBasis F) (ch : Challenges K) : Payload K Bat :=
  PayloadSplit.roundInclusion (PayloadSplit.originalRounds pub B ch 0) - k0 pub B ch • dir +
    msCell (S0 pub B ch)

/-! ### Silent values -/

theorem roundPoly_msCell (j : Fin 10) (s : K) : Chain.roundPoly j (msCell (Bat := Bat) s) = 0 := by
  rw [Chain.roundPoly_apply]
  simp only [msCell_semanticCoeff, monomial_zero_right, Finset.sum_const_zero]

theorem iota_msCell (s : K) : HonestValid.iota (msCell (Bat := Bat) s) = -s := by
  simp only [HonestValid.iota_apply, roundPoly_msCell, msCell_maskSum, eval_zero, zero_add,
    zero_sub]

theorem iota_refPayload (pub : Public K) (B : PackBasis F) (ch : Challenges K) :
    HonestValid.iota (refPayload (Bat := Bat) pub B ch) = 0 := by
  rw [refPayload, map_add, map_sub, map_smul, HonestValid.iota_originalRounds, HonestValid.iota_dir,
    iota_msCell, smul_zero, sub_zero]
  unfold S0
  ring

/-- Every cell other than the round cells and `.maskSum` is zero. -/
theorem refPayload_cell (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (cell : PayloadCell Bat) (hc : ∀ j i, cell ≠ .semanticCoeff j i) (hm : cell ≠ .maskSum) :
    refPayload (Bat := Bat) pub B ch cell = 0 := by
  cases cell with
  | semanticCoeff j i => exact absurd rfl (hc j i)
  | maskSum => exact absurd rfl hm
  | pointClaim j c => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring
  | extraClaim c => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring
  | ood j c => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring
  | inactiveSum => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring
  | opened q s c => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring
  | bat b => show (0 : K) - k0 pub B ch * 0 + 0 = 0; ring

theorem inactive_refPayload (pub : Public K) (B : PackBasis F) (ch : Challenges K) :
    refPayload (Bat := Bat) pub B ch .inactiveSum = 0 :=
  refPayload_cell pub B ch .inactiveSum (by intro _ _ h; cases h) (by intro h; cases h)

theorem Phi0_msCell (B : PackBasis F) (ch : Challenges K) (s : K) :
    Phi0 B ch (msCell (Bat := Bat) s) = 0 := by
  have hr : round9Poly (msCell (Bat := Bat) s) = 0 := by
    rw [round9Poly_apply]
    simp only [msCell_semanticCoeff, monomial_zero_right, Finset.sum_const_zero]
  have hc : claimMask B (alpha ch) (msCell (Bat := Bat) s) = 0 := by
    simp only [claimMask, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      proj_apply, msCell_pointClaim, msCell_extraClaim, smul_zero, Finset.sum_const_zero, add_zero]
  simp only [Phi0, LinearMap.sub_apply, evalRound9_apply, hr, hc, eval_zero, sub_zero]

theorem Phi0_refPayload (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (hhalf : alpha ch 9 ≠ 1/2) : Phi0 B ch (refPayload (Bat := Bat) pub B ch) = 0 := by
  rw [refPayload, map_add, map_sub, map_smul, Phi0_roundInclusion, evalRound9_originalRounds,
    Phi0_dir, Phi0_msCell, smul_eq_mul, add_zero]
  unfold k0
  have hne : alpha ch 9 - 1/2 ≠ 0 := sub_ne_zero.mpr hhalf
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, sub_self]

theorem msCell_mem_chainEqs (ch : Challenges K) (s : K) :
    msCell (Bat := Bat) s ∈ IIPrimeResidual.ChainEqs ch := by
  rw [IIPrimeResidual.mem_chainEqs_iff]
  intro j
  simp only [roundPoly_msCell, eval_zero, add_zero]

theorem refPayload_mem_chainEqs (pub : Public K) (B : PackBasis F) (ch : Challenges K) :
    refPayload (Bat := Bat) pub B ch ∈ IIPrimeResidual.ChainEqs ch :=
  (IIPrimeResidual.ChainEqs ch).add_mem
    ((IIPrimeResidual.ChainEqs ch).sub_mem
      (IIPrimeResidual.originalRounds_mem_chainEqs pub B ch 0)
      ((IIPrimeResidual.ChainEqs ch).smul_mem _ (IIPrimeResidual.dir_mem_chainEqs ch)))
    (msCell_mem_chainEqs ch _)

/-- `k₀ ∈ K₄` from `TerminalClosed` (the zero trace has zero claims). -/
theorem k0_mem (B : PackBasis F) (hB : PackField B) (pub : Public K) (ch : Challenges K)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) (hT : K4Values.TerminalClosed (K4 B hB) pub B ch) :
    k0 pub B ch ∈ K4 B hB := by
  have ha : ∀ i, alpha ch i ∈ K4 B hB := K4Values.alpha_mem _ ch hsem
  have h0 : ∀ c r, (0 : Trace K) c r ∈ K4 B hB := fun _ _ => (K4 B hB).zero_mem
  unfold k0 fOrig
  refine (K4 B hB).mul_mem ((K4 B hB).mul_mem (hsem 14) (hT _ _ (fun j c =>
    K4Values.honestClaims_mem _ _ h0 _ ha j c) ha)) ?_
  exact (K4 B hB).inv_mem ((K4 B hB).sub_mem (ha 9) (half_mem_K4 B hB))

/-- The round cells of `refPayload` lie in `K₄`. -/
theorem refPayload_round_mem (B : PackBasis F) (hB : PackField B) (pub : Public K)
    (ch : Challenges K) (hsem : ∀ i, ch.sem i ∈ K4 B hB)
    (hT : K4Values.TerminalClosed (K4 B hB) pub B ch) (j : Fin 10) (i : Fin 28) :
    refPayload (Bat := Bat) pub B ch (.semanticCoeff j i) ∈ K4 B hB := by
  show PayloadSplit.originalRounds pub B ch 0 j i -
      k0 pub B ch * (if j = 9 then (X - C (1 / 2 : K)).coeff i.val else 0) + 0 ∈ K4 B hB
  exact (K4 B hB).add_mem ((K4 B hB).sub_mem
    (K4Values.originalRounds_mem _ pub B ch hsem hT 0 (fun _ _ => (K4 B hB).zero_mem) j i)
    ((K4 B hB).mul_mem (k0_mem B hB pub ch hsem hT) (K4Values.dirCoeff_mem B hB j i)))
    (K4 B hB).zero_mem

/-! ### The explicit simulator -/

/-- ZF2's simulator: the shifted reference coset at a uniform tape.  Its
arguments are public; there is no instance and no choice. -/
def simE (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) (ch : Challenges K) (t : JointView.Tape K F) :
    JointView.View K CommitHandle Aux Bat :=
  (ZkStatement.metadata outputs x ch,
    shift x.1 B ch (refPayload x.1 B ch + A π B ch (Partition.equiv.symm t)))

attribute [local irreducible] JointView.payload A g

/-- Clause (i′) for `w` and the reference coset give equal laws of the honest
view and `simE`. -/
theorem equalLaws_simE_of [Fintype Bat] (h : JointView.HonestProver K) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) (w : h.Instance) (ch : Challenges K)
    (hi : ∀ n, sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM))
    (hz : cTilde (Bat := Bat) h B x w ch - refPayload x.1 B ch ∈ LinearMap.range (A h.transport B ch)) :
    EqualLaws (JointView.view (Bat := Bat) h B outputs x w ch) (simE h.transport B outputs x ch) := by
  have hlaw := payload_law_on h B x w ch hi
  have hlinear := AffineLaw.equal_laws_of_mask_image (A h.transport B ch) (A h.transport B ch)
    (cTilde h B x w ch) (refPayload x.1 B ch) rfl hz
  have hshift := equalLaws_comp (shift x.1 B ch) hlinear
  have hpart : EqualLaws (D12.payload (Bat := Bat) h B x w ch)
      (fun t => shift x.1 B ch (refPayload x.1 B ch + A h.transport B ch t)) := by
    intro v
    exact (hlaw v).trans (hshift v)
  have hold : EqualLaws (JointView.payload (Bat := Bat) h B x w ch)
      (fun t => shift x.1 B ch (refPayload x.1 B ch + A h.transport B ch (Partition.equiv.symm t))) := by
    refine AbsorptionLaw.equal_laws_of_equiv Partition.equiv.toEquiv _ _ ?_
    have hg : ∀ r : T K F, Partition.equiv.symm (Partition.equiv.toEquiv r) = r :=
      fun r => Partition.equiv.symm_apply_apply r
    simp only [hg]
    unfold R0Z.D12.payload at hpart
    exact hpart
  have hp := AffineLaw.equal_laws_const_pair (JointView.payload (Bat := Bat) h B x w ch)
    (fun t => shift x.1 B ch (refPayload x.1 B ch + A h.transport B ch (Partition.equiv.symm t)))
    (ZkStatement.metadata outputs x ch) hold
  unfold JointView.view simE
  exact hp

#print axioms msCell
#print axioms k0
#print axioms S0
#print axioms refPayload
#print axioms roundPoly_msCell
#print axioms iota_msCell
#print axioms iota_refPayload
#print axioms refPayload_cell
#print axioms inactive_refPayload
#print axioms Phi0_msCell
#print axioms Phi0_refPayload
#print axioms msCell_mem_chainEqs
#print axioms refPayload_mem_chainEqs
#print axioms k0_mem
#print axioms refPayload_round_mem
#print axioms simE
#print axioms equalLaws_simE_of
end R0Z.RefPayload
