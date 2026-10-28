import R0Z.K4
import R0Z.PureRounds

/-! J3 (T2b-2b design §2.1, §5; DESIGN-T2b-2b-Dprime §2.1, §6): the
structural reduction of `Chain0₄ ⊆ silent image` to the round cover (Q′) and
the batched condition (B).

* `exists_silent_of_cover` is payload-generic linear algebra over any ring.
* `ownMap`, `batMap`, `ia_pure_zero`, `ms_pure_eq_initial`, `QPrime`, `BCond`
  and `chain0K4_le_silent_of` are the R0 instantiation.  `BCond` is exactly
  the premise "B-open" of D23.2: `(ker own ⊓ ker R).map bat = (ker own).map bat`.
* `ownMap` keeps the direct observations `.pointClaim`, `.extraClaim`, `.ood`,
  `.opened` on all 29 columns; `batMap` reads the batched cells `.bat b`
  (for R0, `.openingCoeff` and `.finalCoeff`), valued in `Bat → K` (R1-0).

Nothing here asserts (Q′) or (B); both enter `chain0K4_le_silent_of` as
named hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.SilentReduction
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView
  R0Z.Partition R0Z.D12 R0Z.Shift R0Z.Chain R0Z.Z4Maps R0Z.PureRounds R0Z.K4 Polynomial
attribute [local irreducible] copyInactiveRows

/-! ### Generic reduction -/

/-- Design §2.1: (Q′) and (B) give every target vector as the round image of
a tape that is silent for `o` and `b`. -/
theorem exists_silent_of_cover {R V W₁ W₂ W₃ : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂] [AddCommGroup W₃] [Module R W₃]
    (Rm : V →ₗ[R] W₁) (o : V →ₗ[R] W₂) (b : V →ₗ[R] W₃) (T : Submodule R W₁)
    (hQ : T ≤ (LinearMap.ker o).map Rm)
    (hB : (LinearMap.ker o ⊓ LinearMap.ker Rm).map b = (LinearMap.ker o).map b) :
    T ≤ (LinearMap.ker o ⊓ LinearMap.ker b).map Rm := by
  intro t ht
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 (hQ ht)
  have hbx : b x ∈ (LinearMap.ker o).map b := Submodule.mem_map.2 ⟨x, hx, rfl⟩
  rw [← hB] at hbx
  obtain ⟨y, hy, hyb⟩ := Submodule.mem_map.1 hbx
  obtain ⟨hyo, hyR⟩ := Submodule.mem_inf.1 hy
  refine Submodule.mem_map.2 ⟨x - y, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, LinearMap.mem_ker.1 hx, LinearMap.mem_ker.1 hyo, sub_zero]
  · rw [LinearMap.mem_ker, map_sub, hyb, sub_self]
  · rw [map_sub, LinearMap.mem_ker.1 hyR, sub_zero]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ### Observation maps on the mask tape -/

/-- Keep the per-lane direct observations; zero every other cell. -/
def ownProj : Payload K Bat →ₗ[F] Payload K Bat :=
  LinearMap.pi fun coord => match coord with
  | .pointClaim j c => (LinearMap.proj (.pointClaim j c) : Payload K Bat →ₗ[F] K)
  | .extraClaim c => (LinearMap.proj (.extraClaim c) : Payload K Bat →ₗ[F] K)
  | .ood j c => (LinearMap.proj (.ood j c) : Payload K Bat →ₗ[F] K)
  | .opened q s c => (LinearMap.proj (.opened q s c) : Payload K Bat →ₗ[F] K)
  | _ => 0

/-- Read the batched opening cells (R1-0: replaces R0's `batProj`). -/
def batRead : Payload K Bat →ₗ[F] (Bat → K) :=
  LinearMap.pi fun b => (LinearMap.proj (PayloadCell.bat b) : Payload K Bat →ₗ[F] K)

/-- `own m`: claims, extra claims, OOD values and opened symbols of `A(inlM m)`. -/
def ownMap (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    M K F →ₗ[F] Payload K Bat :=
  (ownProj (F := F)).comp ((A (Bat := Bat) π B ch).comp inlM)

/-- `bat m`: the batched cells of `A(inlM m)` (for R0, `.openingCoeff` and
`.finalCoeff`). -/
def batMap (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    M K F →ₗ[F] (Bat → K) :=
  (batRead (F := F)).comp ((A (Bat := Bat) π B ch).comp inlM)

/-! ### The inactive sum vanishes on mask tapes (balance) -/

/-- Generic cancellation in `K`: the set and both decidability instances are
arguments, so they are unified from the goal rather than synthesized, and no
concrete row set is ever reduced. -/
theorem balance_sum_generic {ι : Type*} (S : Finset ι) (d : ι)
    (instE : DecidableEq ι) (instI : (r : ι) → Decidable (r = d)) (hd : d ∈ S) (g : ι → K) :
    ∑ r ∈ S, @ite K (r = d) (instI r) (-(∑ s ∈ @Finset.erase ι instE S d, g s)) (g r) = 0 := by
  letI : DecidableEq ι := instE
  rw [← Finset.add_sum_erase S _ hd]
  have he : ∑ r ∈ S.erase d, @ite K (r = d) (instI r) (-(∑ s ∈ S.erase d, g s)) (g r) =
      ∑ r ∈ S.erase d, g r :=
    Finset.sum_congr rfl (fun r hr => if_neg (Finset.ne_of_mem_erase hr))
  rw [if_pos rfl, he]
  exact neg_add_cancel _

/-- The same cancellation for a balanced family of linear maps, evaluated at a
point; instances again come from the goal. -/
theorem balance_apply_sum_generic {ι V : Type*} [AddCommGroup V] [Module F V]
    (S : Finset ι) (d : ι) (instE : DecidableEq ι) (instI : (r : ι) → Decidable (r = d))
    (hd : d ∈ S) (f : ι → V →ₗ[F] K) (p : V) :
    ∑ r ∈ S, (@ite (V →ₗ[F] K) (r = d) (instI r)
      (-(∑ s ∈ @Finset.erase ι instE S d, f s)) (f r)) p = 0 := by
  have e : ∀ r ∈ S, (@ite (V →ₗ[F] K) (r = d) (instI r)
      (-(∑ s ∈ @Finset.erase ι instE S d, f s)) (f r)) p =
      @ite K (r = d) (instI r) (-(∑ s ∈ @Finset.erase ι instE S d, f s p)) (f r p) := by
    intro r _
    by_cases h : r = d
    · rw [if_pos h, if_pos h, LinearMap.neg_apply, LinearMap.sum_apply]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl e]
  exact balance_sum_generic S d instE instI hd (fun r => f r p)

/-- A balanced family sums to zero over the inactive rows, at every tape. -/
theorem balanceAff_sum_apply (f : Fin 1024 → AffTape K F →ₗ[F] K) (p : AffTape K F) :
    ∑ r ∈ copyInactiveRows, balanceAff 0 f r p = 0 := by
  have h0 : (0 : Fin 1024) ∈ copyInactiveRows :=
    (R0Z.TerminalEligible.mem_inactive 0).2 R0Z.TerminalEligible.zero_inactive
  unfold balanceAff
  exact balance_apply_sum_generic copyInactiveRows 0 _ _ h0 f p

/-- Every column of the affine trace part sums to zero over the inactive rows. -/
theorem traceLinear_inactive_sum (B : PackBasis F) (p : AffTape K F) (c : Fin 29) :
    ∑ r ∈ copyInactiveRows, traceLinear B p c r = 0 := by
  simp only [traceLinear, LinearMap.pi_apply]
  by_cases h1 : c.val < 16
  · simp only [h1, ↓reduceIte, LinearMap.zero_apply, Finset.sum_const_zero]
  · by_cases h2 : c.val < 26
    · simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
      exact balanceAff_sum_apply _ p
    · by_cases h3 : c.val = 26
      · simp only [h1, h2, ↓reduceIte, ↓reduceDIte, if_pos h3]
        exact balanceAff_sum_apply _ p
      · by_cases h4 : c.val = 27
        · simp only [h1, h2, ↓reduceIte, ↓reduceDIte, if_neg h3, if_pos h4]
          exact balanceAff_sum_apply _ p
        · simp only [h1, h2, ↓reduceIte, ↓reduceDIte, if_neg h3, if_neg h4]
          exact balanceAff_sum_apply _ p

theorem pureTrace_inactive_dot (B : PackBasis F) (m : M K F) (c : Fin 29) :
    dotLinear (AspisR0.Opening.indicator copyInactiveRows) (pureTrace B m c) = 0 := by
  unfold dotLinear
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply]
  have hi (i : Fin 1024) :
      (AspisR0.Opening.indicator copyInactiveRows i : K) • pureTrace B m c i =
      if i ∈ copyInactiveRows then pureTrace B m c i else 0 := by
    unfold AspisR0.Opening.indicator
    by_cases h : i ∈ copyInactiveRows
    · simp only [h, ↓reduceIte, one_smul]
    · simp only [h, ↓reduceIte, zero_smul]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_ite_mem, Finset.univ_inter]
  exact traceLinear_inactive_sum B (pureAff m) c

/-- `L` at `.inactiveSum` is the linear payload there (one definitional step;
`L` itself is not unfolded by `simp`, whose `.maskSum` branch sums over the
Boolean cube). -/
theorem L_inactiveSum (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) :
    PayloadSplit.L (Bat := Bat) π B ch t .inactiveSum = linearPayload (Bat := Bat) π ch t .inactiveSum := rfl

section LRead
/- As in Shift.LRead: keep the large readers opaque while `simp` reduces the
payload match. -/
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks
  claimsLinear extraLinear dotLinear honestClaims batchLinear

theorem linearPayload_inactiveSum (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (t : Trace K) :
    linearPayload (Bat := Bat) π ch t .inactiveSum = ∑ c : Fin 29, ch.opening 0 ^ c.val *
      dotLinear (AspisR0.Opening.indicator copyInactiveRows) (t c) := by
  simp only [linearPayload, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]

end LRead

/-- Design §2.2.1: `.inactiveSum` is identically zero on mask tapes. -/
theorem ia_pure_zero (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) : (A (Bat := Bat) π B ch).comp inlM m .inactiveSum = 0 := by
  rw [A_pure, L_inactiveSum, linearPayload_inactiveSum]
  exact Finset.sum_eq_zero (fun c _ => by rw [pureTrace_inactive_dot, mul_zero])

/-- `.maskSum` on a mask tape is the initial sum `p₀(0) + p₀(1)` of its rounds. -/
theorem ms_pure_eq_initial (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) :
    (A (Bat := Bat) π B ch).comp inlM m .maskSum =
      (roundPoly 0 ((A (Bat := Bat) π B ch).comp inlM m)).eval 0 +
        (roundPoly 0 ((A (Bat := Bat) π B ch).comp inlM m)).eval 1 := by
  rw [A_pure, roundPoly_L, rounds_initial ch _ (maskLinear_vdeg _ B _), bsumB_eq_sum,
    L_maskSum]
  try rfl

/-! ### Target spaces -/

/-- Round vectors with the nine chain equalities and terminal `p₉(α₉) = 0`;
the initial sum is free (design §2.1, `Chain_T0`). -/
def ChainT0 (ch : Challenges K) : Submodule K (PayloadSplit.RoundPayload K) :=
  ((⨅ j : Fin 9, LinearMap.ker
      (evalRound j.succ 0 + evalRound j.succ 1 - evalRound j.castSucc (alpha ch j.castSucc))) ⊓
    LinearMap.ker (evalRound 9 (alpha ch 9))).comap (PayloadSplit.roundInclusion (Bat := Bat))

theorem mem_chainT0_iff (ch : Challenges K) (t : PayloadSplit.RoundPayload K) :
    t ∈ ChainT0 (Bat := Bat) ch ↔
      (∀ j : Fin 9, (roundPoly j.succ (PayloadSplit.roundInclusion (Bat := Bat) t)).eval 0 +
          (roundPoly j.succ (PayloadSplit.roundInclusion (Bat := Bat) t)).eval 1 =
        (roundPoly j.castSucc (PayloadSplit.roundInclusion (Bat := Bat) t)).eval (alpha ch j.castSucc)) ∧
      (roundPoly 9 (PayloadSplit.roundInclusion (Bat := Bat) t)).eval (alpha ch 9) = 0 := by
  simp only [ChainT0, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.add_apply, LinearMap.sub_apply, evalRound_apply, sub_eq_zero]

/-- Round vectors with every coefficient in `K₄`. -/
def K4Round (B : PackBasis F) (hB : PackField B) : Submodule F (PayloadSplit.RoundPayload K) :=
  ⨅ j : Fin 10, ⨅ i : Fin 28, (K4F B hB).comap
    ((LinearMap.proj i : (Fin 28 → K) →ₗ[F] K).comp
      (LinearMap.proj j : PayloadSplit.RoundPayload K →ₗ[F] (Fin 28 → K)))

theorem mem_K4Round_iff (B : PackBasis F) (hB : PackField B) (t : PayloadSplit.RoundPayload K) :
    t ∈ K4Round B hB ↔ ∀ j i, t j i ∈ K4 B hB := by
  simp only [K4Round, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
    LinearMap.proj_apply, mem_K4F]

/-- `Chain_T0₄`: K₄-valued `Chain_T0` (F-dimension 1,080 on Z8c's vectors). -/
def ChainT0K4 (B : PackBasis F) (hB : PackField B) (ch : Challenges K) :
    Submodule F (PayloadSplit.RoundPayload K) :=
  (ChainT0 (Bat := Bat) ch).restrictScalars F ⊓ K4Round B hB

/-- Payload vectors with every cell in `K₄`. -/
def K4Payload (B : PackBasis F) (hB : PackField B) : Submodule F (Payload K Bat) :=
  ⨅ cell : PayloadCell Bat, (K4F B hB).comap (LinearMap.proj cell : Payload K Bat →ₗ[F] K)

/-- Design §1.3: `Chain0₄ = Chain0 ∩ K₄`-valued cells. -/
def Chain0K4 (B : PackBasis F) (hB : PackField B) (ch : Challenges K) :
    Submodule F (Payload K Bat) :=
  (Chain0 ch).restrictScalars F ⊓ K4Payload B hB

theorem mem_chain0K4_iff (B : PackBasis F) (hB : PackField B) (ch : Challenges K)
    (v : Payload K Bat) : v ∈ Chain0K4 B hB ch ↔ v ∈ Chain0 ch ∧ ∀ cell, v cell ∈ K4 B hB := by
  simp only [Chain0K4, K4Payload, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply, mem_K4F]

/-! ### The two premises -/

/-- (Q′), design §2.1: every `Chain_T0₄` vector is the round image of an
own-silent mask tape. -/
def QPrime (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) : Prop :=
  ChainT0K4 (Bat := Bat) B hB ch ≤
    (LinearMap.ker (ownMap (Bat := Bat) π B ch)).map (roundMaskMap (Bat := Bat) π B ch)

/-- (B), DESIGN-T2b-2b-Dprime §2.1 / LOG D23.2 ("B-open"): the batched
coordinates reach on own-silent round-kernel tapes what they reach on all
own-silent tapes. -/
def BCond (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Prop :=
  (LinearMap.ker (ownMap (Bat := Bat) π B ch) ⊓ LinearMap.ker (roundMaskMap (Bat := Bat) π B ch)).map
      (batMap (Bat := Bat) π B ch) =
    (LinearMap.ker (ownMap (Bat := Bat) π B ch)).map (batMap (Bat := Bat) π B ch)

/-! ### The reduction -/

/-- Two payloads with the same non-round cells and the same round cells agree. -/
theorem payload_ext {v w : Payload K Bat} (h1 : nonRound (F := F) v = nonRound (F := F) w)
    (h2 : roundProjection (F := F) v = roundProjection (F := F) w) : v = w := by
  funext cell
  cases cell with
  | semanticCoeff j i => exact congrFun (congrFun h2 j) i
  | maskSum => exact congrFun h1 .maskSum
  | pointClaim j c => exact congrFun h1 (.pointClaim j c)
  | extraClaim c => exact congrFun h1 (.extraClaim c)
  | ood j c => exact congrFun h1 (.ood j c)
  | inactiveSum => exact congrFun h1 .inactiveSum
  | opened q s c => exact congrFun h1 (.opened q s c)
  | bat b => exact congrFun h1 (.bat b)

theorem roundPoly_eq_of_roundProjection {v w : Payload K Bat}
    (h : roundProjection (F := F) v = roundProjection (F := F) w) (j : Fin 10) :
    roundPoly j v = roundPoly j w := by
  rw [Chain.roundPoly_apply, Chain.roundPoly_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hji : v (.semanticCoeff j i) = w (.semanticCoeff j i) := congrFun (congrFun h j) i
  rw [hji]

/-- A mask tape with zero own, zero batched cells and zero initial round sum
is silent. -/
theorem mem_silentMasks_of (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) (hown : ownMap (Bat := Bat) π B ch m = 0) (hbat : batMap (Bat := Bat) π B ch m = 0)
    (hinit : (roundPoly 0 ((A (Bat := Bat) π B ch).comp inlM m)).eval 0 +
        (roundPoly 0 ((A (Bat := Bat) π B ch).comp inlM m)).eval 1 = 0) :
    m ∈ silentMasks (Bat := Bat) π B ch := by
  show nonRound (F := F) ((A (Bat := Bat) π B ch).comp inlM m) = 0
  funext cell
  cases cell with
  | semanticCoeff j i => rfl
  | maskSum =>
    change (A (Bat := Bat) π B ch).comp inlM m .maskSum = 0
    rw [ms_pure_eq_initial]
    exact hinit
  | pointClaim j c =>
    simpa only [ownMap, ownProj, batMap, batRead, nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown (.pointClaim j c)
  | extraClaim c =>
    simpa only [ownMap, ownProj, batMap, batRead, nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown (.extraClaim c)
  | ood j c =>
    simpa only [ownMap, ownProj, batMap, batRead, nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown (.ood j c)
  | inactiveSum =>
    simpa only [nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Pi.zero_apply] using ia_pure_zero π B ch m
  | opened q s c =>
    simpa only [ownMap, ownProj, batMap, batRead, nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hown (.opened q s c)
  | bat b =>
    simpa only [ownMap, ownProj, batMap, batRead, nonRound, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hbat b

/-- Design §2.1 / D23: (Q′) and (B) give `Chain0₄ ⊆ A(inlM(silentMasks))`. -/
theorem chain0K4_le_silent_of (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (hB : PackField B) (ch : Challenges K)
    (hQ : QPrime (Bat := Bat) π B hB ch) (hBc : BCond (Bat := Bat) π B ch) :
    Chain0K4 (Bat := Bat) B hB ch ≤ (silentMasks (Bat := Bat) π B ch).map ((A (Bat := Bat) π B ch).comp inlM) := by
  intro v hv
  obtain ⟨hvC, hvK⟩ := (mem_chain0K4_iff B hB ch v).1 hv
  obtain ⟨hnr, hinit, hchain, hterm⟩ := (mem_chain0_iff (F := F) ch v).1 hvC
  let t : PayloadSplit.RoundPayload K := roundProjection (F := F) v
  have hvt : PayloadSplit.roundInclusion t = v := by
    apply payload_ext (F := F)
    · rw [hnr]
      exact nonRound_roundInclusion (F := F) t
    · rfl
  have ht : t ∈ ChainT0K4 (Bat := Bat) B hB ch := by
    refine Submodule.mem_inf.2 ⟨?_, (mem_K4Round_iff B hB t).2 (fun j i => hvK _)⟩
    rw [Submodule.restrictScalars_mem, mem_chainT0_iff, hvt]
    exact ⟨hchain, hterm⟩
  obtain ⟨m, hm, hRm⟩ := Submodule.mem_map.1
    (exists_silent_of_cover (roundMaskMap (Bat := Bat) π B ch) (ownMap (Bat := Bat) π B ch)
      (batMap (Bat := Bat) π B ch) _ hQ hBc ht)
  obtain ⟨hown, hbat⟩ := Submodule.mem_inf.1 hm
  have hproj : roundProjection (F := F) ((A (Bat := Bat) π B ch).comp inlM m) = roundProjection (F := F) v :=
    hRm
  have hsil : m ∈ silentMasks (Bat := Bat) π B ch := by
    refine mem_silentMasks_of π B ch m (LinearMap.mem_ker.1 hown) (LinearMap.mem_ker.1 hbat) ?_
    rw [roundPoly_eq_of_roundProjection hproj 0]
    exact hinit
  refine Submodule.mem_map.2 ⟨m, hsil, ?_⟩
  apply payload_ext (F := F)
  · rw [hnr]
    exact hsil
  · exact hproj

#print axioms exists_silent_of_cover
#print axioms balance_sum_generic
#print axioms balance_apply_sum_generic
#print axioms balanceAff_sum_apply
#print axioms traceLinear_inactive_sum
#print axioms pureTrace_inactive_dot
#print axioms L_inactiveSum
#print axioms linearPayload_inactiveSum
#print axioms ia_pure_zero
#print axioms ms_pure_eq_initial
#print axioms mem_chainT0_iff
#print axioms mem_K4Round_iff
#print axioms mem_chain0K4_iff
#print axioms payload_ext
#print axioms roundPoly_eq_of_roundProjection
#print axioms mem_silentMasks_of
#print axioms chain0K4_le_silent_of

end R0Z.SilentReduction
