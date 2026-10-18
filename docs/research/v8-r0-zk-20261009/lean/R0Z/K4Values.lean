import R0Z.SilentReduction

/-! J2 / J2-R1 (DESIGN-T2b-2b §5 J2; DESIGN-R1-PRIVACY-MODEL §4 J2-R1):
`sRem ∈ Chain0K4`, stated once for every batched layer `Bat` (R0 and R1).

The remainder `sRem` is supported on the ten round arrays; its cells are the
coefficient differences `g` of the original-terminal round polynomials of two
actual traces, minus a multiple of the direction `X − ½`.  This module proves:

* `interpolate_mem`: Lagrange interpolation on the nodes `0, …, 27` with values
  in a subfield `S` has every coefficient in `S`;
* `actual_mem`: every cell of an actual (masked, prepared) trace lies in `K₄`
  when the instance is base-typed and `λ, χ ∈ K₄` (the H1 helper column
  included, `helper_mem`);
* `honestClaims_mem`, `roundPoint_mem`, `originalRounds_mem`, `g_mem`;
* `sRem_mem_K4` and `sRem_mem_chain0K4`.

One closure fact about the R0P terminal is NOT proved here and enters as the
named premise `TerminalClosed S pub B ch`: the terminal value
`terminalValue pub λ χ θ μ zc B y a` lies in `S` whenever the claims `y` and
the point `a` do.  It is a pure field-closure property of the ported
constraint families (`laneAt`: Poseidon, schedule, occupancy, path, value,
digest, asset, copy), given the challenges in `S` and the public statement in
the base field. -/

set_option autoImplicit false

noncomputable section

namespace R0Z.K4Values

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.Shift
  R0Z.K4 Polynomial

attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ## Polynomials with coefficients in a subfield -/

/-- Polynomials all of whose coefficients lie in `S`. -/
def coeffRing (S : Subfield K) : Subring K[X] where
  carrier := {p | ∀ n, p.coeff n ∈ S}
  mul_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_mul]
    exact sum_mem fun x _ => S.mul_mem (hp _) (hq _)
  one_mem' := by
    intro n
    rw [Polynomial.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_add]
    exact S.add_mem (hp n) (hq n)
  zero_mem' := by
    intro n
    rw [Polynomial.coeff_zero]
    exact S.zero_mem
  neg_mem' := by
    intro p hp n
    rw [Polynomial.coeff_neg]
    exact S.neg_mem (hp n)

theorem C_mem_coeffRing (S : Subfield K) {c : K} (hc : c ∈ S) : C c ∈ coeffRing S := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact S.zero_mem

theorem X_mem_coeffRing (S : Subfield K) : (X : K[X]) ∈ coeffRing S := by
  intro n
  rw [Polynomial.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

/-- Interpolation on the 28 natural nodes keeps coefficients in `S`. -/
theorem interpolate_mem (S : Subfield K) (v : Fin 28 → K) (hv : ∀ i, v i ∈ S) :
    Lagrange.interpolate Finset.univ (fun i : Fin 28 => (i.val : K)) v ∈ coeffRing S := by
  rw [Lagrange.interpolate_apply]
  refine sum_mem fun i _ => (coeffRing S).mul_mem (C_mem_coeffRing S (hv i)) ?_
  unfold Lagrange.basis
  refine prod_mem fun j _ => ?_
  unfold Lagrange.basisDivisor
  exact (coeffRing S).mul_mem
    (C_mem_coeffRing S (S.inv_mem (S.sub_mem (natCast_mem S _) (natCast_mem S _))))
    ((coeffRing S).sub_mem (X_mem_coeffRing S) (C_mem_coeffRing S (natCast_mem S _)))

theorem interpolate_coeff_mem (S : Subfield K) (v : Fin 28 → K) (hv : ∀ i, v i ∈ S) (d : ℕ) :
    (Lagrange.interpolate Finset.univ (fun i : Fin 28 => (i.val : K)) v).coeff d ∈ S :=
  interpolate_mem S v hv d

/-! ## Points and claims -/

theorem alpha_mem (S : Subfield K) (ch : Challenges K) (hsem : ∀ i, ch.sem i ∈ S)
    (i : Fin 10) : alpha ch i ∈ S := hsem _

theorem roundPoint_mem (S : Subfield K) (ch : Challenges K) (hsem : ∀ i, ch.sem i ∈ S)
    (j : Fin 10) (k : ℕ) (tail : Fin (9 - j.val) → Bool) (i : Fin 10) :
    roundPoint ch j (k : K) tail i ∈ S := by
  unfold roundPoint
  split_ifs
  · exact alpha_mem S ch hsem i
  · exact natCast_mem S k
  · exact S.one_mem
  · exact S.zero_mem

theorem eqWeight_mem (S : Subfield K) (p : Fin 10 → K) (hp : ∀ i, p i ∈ S) (r : Fin 1024) :
    AspisR0.Opening.eqWeight p r ∈ S := by
  unfold AspisR0.Opening.eqWeight
  refine prod_mem fun b _ => ?_
  split_ifs
  · exact S.sub_mem S.one_mem (hp b)
  · exact hp b

theorem succCarry_mem (S : Subfield K) (p : Fin 10 → K) (hp : ∀ i, p i ∈ S) :
    ∀ k, succCarry p k ∈ S
  | 0 => S.one_mem
  | k + 1 => by
    unfold succCarry
    refine S.mul_mem ?_ (succCarry_mem S p hp k)
    split_ifs
    · exact hp _
    · exact S.zero_mem

theorem openingPoints_mem (S : Subfield K) (a : Fin 10 → K) (ha : ∀ i, a i ∈ S)
    (j : Fin 3) (i : Fin 10) : openingPoints a j i ∈ S := by
  match j with
  | 0 => exact ha _
  | 1 =>
    show successorPoint a ⟨9 - i.val, by omega⟩ ∈ S
    unfold successorPoint
    have hc := succCarry_mem S a ha (9 - (9 - i.val))
    exact S.sub_mem (S.add_mem (ha _) hc)
      (S.add_mem (S.mul_mem (ha _) hc) (S.mul_mem (ha _) hc))
  | 2 =>
    show xor12Point a ⟨9 - i.val, by omega⟩ ∈ S
    unfold xor12Point
    split_ifs
    · exact S.sub_mem S.one_mem (ha _)
    · exact ha _

theorem honestClaims_mem (S : Subfield K) (t : Trace K) (ht : ∀ c r, t c r ∈ S)
    (a : Fin 10 → K) (ha : ∀ i, a i ∈ S) (j : Fin 3) (c : Fin 29) :
    honestClaims t a j c ∈ S := by
  unfold honestClaims AspisR0.LinearDual.dot
  exact sum_mem fun r _ =>
    S.mul_mem (eqWeight_mem S _ (openingPoints_mem S a ha j) r) (ht c r)

/-! ## The H1 helper column -/

theorem copyLinkWeight_mem (S : Subfield K) (link : CopyLink) (n : ℕ) (v : Variant) :
    copyLinkWeight (K := K) link n v ∈ S := by
  unfold copyLinkWeight
  split
  · exact S.one_mem
  · split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · exact natCast_mem S _
  · exact natCast_mem S _

theorem copyTupleValue_mem (S : Subfield K) (t : Trace K)
    (ht : ∀ c r, c.val < 16 → t c r ∈ S) (lam : K) (hlam : lam ∈ S) (tag : ℕ)
    (ep : CopyEndpoint) : copyTupleValue lam (copyEndpointTuple t tag ep) ∈ S := by
  unfold copyTupleValue copyEndpointTuple copyPatternTuple
  refine S.add_mem (natCast_mem S tag) (sum_mem fun i _ => S.mul_mem (S.pow_mem hlam _) ?_)
  try dsimp only
  split_ifs
  · exact S.add_mem (ht _ _ (by simp only [Fin.val_castLE]; exact Fin.isLt _)) (natCast_mem S _)
  · exact S.zero_mem

theorem copyRowValues_mem (S : Subfield K) (t : Trace K)
    (ht : ∀ c r, c.val < 16 → t c r ∈ S) (lam : K) (hlam : lam ∈ S) (b : Fin 1024)
    (endpoint : CopyLink → CopyEndpoint) (slot : Fin 2) :
    copyRowValues t lam b endpoint slot ∈ S := by
  unfold copyRowValues
  refine list_sum_mem fun x hx => ?_
  obtain ⟨link, _, rfl⟩ := List.mem_map.1 hx
  try dsimp only
  split_ifs
  · exact copyTupleValue_mem S t ht lam hlam _ _
  · exact S.zero_mem

theorem copyRowWeights_mem (S : Subfield K) (pub : Public K) (b : Fin 1024)
    (endpoint : CopyLink → CopyEndpoint) (slot : Fin 2) :
    copyRowWeights pub b endpoint slot ∈ S := by
  unfold copyRowWeights
  refine list_sum_mem fun x hx => ?_
  obtain ⟨link, _, rfl⟩ := List.mem_map.1 hx
  try dsimp only
  split_ifs
  · exact copyLinkWeight_mem S _ _ _
  · exact S.zero_mem

/-- The H1 helper (logup reciprocals) stays in `S`. -/
theorem helper_mem (S : Subfield K) (pub : Public K) (t : Trace K)
    (ht : ∀ c r, c.val < 16 → t c r ∈ S) (lam chi : K) (hlam : lam ∈ S) (hchi : chi ∈ S)
    (r : Fin 1024) : helper pub t lam chi r ∈ S := by
  unfold helper
  try dsimp only
  refine S.sub_mem (sum_mem fun s _ => S.mul_mem (S.inv_mem (S.sub_mem hchi ?_)) ?_)
    (sum_mem fun s _ => S.mul_mem (S.inv_mem (S.sub_mem hchi ?_)) ?_)
  · exact copyRowValues_mem S t ht lam hlam r _ s
  · exact copyRowWeights_mem S pub r _ s
  · exact copyRowValues_mem S t ht lam hlam r _ s
  · exact copyRowWeights_mem S pub r _ s

/-! ## The actual trace -/

theorem balance_mem (S : Subfield K) (dep : Fin 1024) (word : Fin 1024 → K)
    (hw : ∀ s, word s ∈ S) (r : Fin 1024) : balance dep word r ∈ S := by
  unfold balance
  split_ifs
  · exact S.neg_mem (sum_mem fun s _ => hw s)
  · exact hw r

/-- Every cell of an actual trace lies in `K₄`: base-typed semantic lanes and
F-valued noise, K₄-packed G/H1/D limbs, and the helper column. -/
theorem actual_mem (B : PackBasis F) (hB : PackField B) (pub : Public K) (t : Trace K)
    (ch : Challenges K) (hF : BaseTyped F t) (hlam : ch.sem 0 ∈ K4 B hB)
    (hchi : ch.sem 1 ∈ K4 B hB) (r : T K F) (c : Fin 29) (s : Fin 1024) :
    PayloadSplit.actual pub B t ch r c s ∈ K4 B hB := by
  have hFK : ∀ x : F, (x : K) ∈ K4 B hB := fun x => F_le_K4 B hB x.2
  have hE : ∀ (c' : Fin 29) (s' : Fin 1024), c'.val < 16 →
      applyEligible t r.2.2 c' s' ∈ K4 B hB := by
    intro c' s' hc'
    unfold applyEligible
    rw [if_pos hc']
    refine balance_mem _ 1023 _ (fun s'' => ?_) s'
    try dsimp only
    refine (K4 B hB).add_mem (F_le_K4 B hB (hF c' (by omega) s'')) ?_
    unfold semanticNoise
    split_ifs
    · exact hFK _
    · exact (K4 B hB).zero_mem
  have hext : ∀ (lane : Fin 3) (q : Fin 1024),
      extensionRaw B (Sum.elim (0 : EligibleNoise K F) (aff r)) lane q ∈ K4 B hB := by
    intro lane q
    exact pack4_mem_K4 B hB _ (fun j => Subtype.mem _)
  unfold PayloadSplit.actual applyAff
  try dsimp only
  split_ifs with h1 h2 h3 h4
  · unfold prepare
    rw [if_neg (by omega)]
    exact hE c s h1
  · unfold maskOnlyColumns
    exact balance_mem _ 0 _ (fun q => hFK _) s
  · refine (K4 B hB).add_mem ?_ ?_
    · unfold prepare
      rw [if_pos h3]
      exact helper_mem _ pub _ hE _ _ hlam hchi s
    · unfold h1Padding
      refine balance_mem _ 0 _ (fun q => ?_) s
      try dsimp only
      split_ifs
      · exact (K4 B hB).zero_mem
      · exact hext 1 q
  · exact balance_mem _ 0 _ (fun q => hext 0 q) s
  · unfold dWord
    exact balance_mem _ 0 _ (fun q => hext 2 q) s

/-! ## Original round polynomials and the remainder -/

/-- The missing field-closure fact about the R0P terminal (see the header). -/
def TerminalClosed (S : Subfield K) (pub : Public K) (B : PackBasis F) (ch : Challenges K) :
    Prop :=
  ∀ (y : Fin 3 → Fin 29 → K) (a : Fin 10 → K), (∀ j c, y j c ∈ S) → (∀ i, a i ∈ S) →
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B y a ∈ S

theorem originalRounds_mem (S : Subfield K) (pub : Public K) (B : PackBasis F)
    (ch : Challenges K) (hsem : ∀ i, ch.sem i ∈ S) (hT : TerminalClosed S pub B ch)
    (t : Trace K) (ht : ∀ c r, t c r ∈ S) (j : Fin 10) (i : Fin 28) :
    PayloadSplit.originalRounds pub B ch t j i ∈ S := by
  unfold PayloadSplit.originalRounds
  rw [PayloadSplit.rounds_apply]
  refine interpolate_coeff_mem S _ (fun k => sum_mem fun tail _ => ?_) i.val
  refine S.mul_mem (hsem 14) (hT _ _ (fun j' c => ?_) (roundPoint_mem S ch hsem j k.val tail))
  exact honestClaims_mem S t ht _ (roundPoint_mem S ch hsem j k.val tail) j' c

theorem g_mem (h : HonestProver K) (B : PackBasis F) (hB : PackField B)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (n : N K F)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) (hF : BaseTyped F (h.build w))
    (hT : TerminalClosed (K4 B hB) x.1 B ch) (j : Fin 10) (i : Fin 28) :
    g h B x w ch n j i ∈ K4 B hB := by
  have hact := fun r => actual_mem B hB x.1 (h.build w) ch hF (hsem 0) (hsem 1) r
  exact (K4 B hB).sub_mem
    (originalRounds_mem _ x.1 B ch hsem hT _ (hact _) j i)
    (originalRounds_mem _ x.1 B ch hsem hT _ (hact _) j i)

theorem dirCoeff_mem (B : PackBasis F) (hB : PackField B) (j : Fin 10) (i : Fin 28) :
    (if j = 9 then (X - C (1 / 2 : K)).coeff i.val else 0) ∈ K4 B hB := by
  split_ifs
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    refine (K4 B hB).sub_mem ?_ ?_
    · split_ifs
      · exact (K4 B hB).one_mem
      · exact (K4 B hB).zero_mem
    · split_ifs
      · exact half_mem_K4 B hB
      · exact (K4 B hB).zero_mem
  · exact (K4 B hB).zero_mem

/-- J2: every cell of `sRem` lies in `K₄`. -/
theorem sRem_mem_K4 (h : HonestProver K) (B : PackBasis F) (hB : PackField B)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (n : N K F)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) (hF : BaseTyped F (h.build w))
    (hT : TerminalClosed (K4 B hB) x.1 B ch) :
    ∀ cell, sRem (Bat := Bat) h B x w ch n cell ∈ K4 B hB := by
  set S := K4 B hB with hS
  let p := g h B x w ch n
  let coef : K := Phi0 B ch (roundInclusion (F := F) (Bat := Bat) p) * (alpha ch 9 - 1 / 2)⁻¹
  have hcell : ∀ cell, sRem (Bat := Bat) h B x w ch n cell =
      PayloadSplit.roundInclusion (Bat := Bat) p cell - coef * dir (K := K) (Bat := Bat) cell :=
    fun cell => rfl
  have hphi : Phi0 B ch (roundInclusion (F := F) (Bat := Bat) p) ∈ S := by
    have e : Phi0 B ch (roundInclusion (F := F) (Bat := Bat) p) =
        evalRound9 ch (PayloadSplit.roundInclusion (Bat := Bat) p) :=
      Phi0_roundInclusion B ch p
    rw [e, evalRound9_roundInclusion, Polynomial.eval_finsetSum]
    refine sum_mem fun i _ => ?_
    rw [Polynomial.eval_monomial]
    exact S.mul_mem (g_mem h B hB x w ch n hsem hF hT 9 i)
      (S.pow_mem (alpha_mem S ch hsem 9) _)
  have hcoef : coef ∈ S :=
    S.mul_mem hphi (S.inv_mem (S.sub_mem (alpha_mem S ch hsem 9) (half_mem_K4 B hB)))
  intro cell
  rw [hcell]
  cases cell with
  | semanticCoeff j i =>
    show p j i - coef * (if j = 9 then (X - C (1 / 2 : K)).coeff i.val else 0) ∈ S
    exact S.sub_mem (g_mem h B hB x w ch n hsem hF hT j i)
      (S.mul_mem hcoef (dirCoeff_mem B hB j i))
  | maskSum =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | pointClaim j c =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | extraClaim c =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | ood j c =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | inactiveSum =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | opened q s c =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem
  | bat b =>
    show (0 : K) - coef * 0 ∈ S
    rw [mul_zero, sub_zero]
    exact S.zero_mem

/-- J2 / J2-R1: `sRem ∈ Chain0₄` for every batched layer (R0 and R1), given
`SemK4`, a base-typed instance, `α₉ ≠ ½`, and `TerminalClosed`. -/
theorem sRem_mem_chain0K4 (h : HonestProver K) (B : PackBasis F) (hB : PackField B)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (n : N K F)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) (hF : BaseTyped F (h.build w))
    (hT : TerminalClosed (K4 B hB) x.1 B ch) (hhalf : alpha ch 9 ≠ 1 / 2) :
    sRem (Bat := Bat) h B x w ch n ∈ R0Z.SilentReduction.Chain0K4 (Bat := Bat) B hB ch :=
  (R0Z.SilentReduction.mem_chain0K4_iff B hB ch _).2
    ⟨R0Z.Chain.sRem_mem_chain0 h B x w ch n hhalf, sRem_mem_K4 h B hB x w ch n hsem hF hT⟩

#print axioms interpolate_mem
#print axioms roundPoint_mem
#print axioms eqWeight_mem
#print axioms openingPoints_mem
#print axioms honestClaims_mem
#print axioms helper_mem
#print axioms actual_mem
#print axioms originalRounds_mem
#print axioms g_mem
#print axioms sRem_mem_K4
#print axioms sRem_mem_chain0K4

end R0Z.K4Values

end
