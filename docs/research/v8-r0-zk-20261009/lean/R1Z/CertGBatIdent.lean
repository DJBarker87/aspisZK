import R1Z.CertGBatK
import R1Z.CertRelWId
import R1Z.RfBat
import Mathlib.Tactic.FinCases

/-! D59.2 / D64.2 (hGBat): the G batched columns are the Rust `unit_functionals` model
`gbatP` (CertGBatK).

* `batMap_read`, `read_cellF`: the batched cells of a mask tape are `cellF b` (round 0, round 1,
  opened folded word, final) applied to the γ-batch `batchR1` of its pure trace.
* `batch_gSrc`: for a G source `(r, k)`, `r ≠ 0`, the batch is
  `γ^27·x_k·(e_{π r} − [r inactive]·e_{π 0})`.
* `round_uvec`, `fold_uvec`, `exact_uvec`: the round polynomial, the coefficient fold and the
  final encoder on a unit vector, symbolically (no sum over the 1,024 coefficients or the
  262,144 points is evaluated).
* `cellF_unit`: every support cell of `e_co` is `ucellP` under the named input premises of
  the relation model (`hA hZx hZy hT hFl hTI`, openings, quarter), the stored first-line points
  `hX` at the opened folded positions and `hfo` (every listed folded position is opened).
* `gbat_cell`, `gbat_ident`: hence the `hGBat` shape from the entry premise
  `Σ_l φ(limb l of cell c of column t) • wb l = gbatP …`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRel

open scoped BigOperators
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
  R0Z.Shift R0Z.Chain R0Z.Z4Maps R1Z.Batched R1Z.RfOwn R1Z.RfSrc R1Z.RfBat
open AspisCircleTensorBinding

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Unit vectors -/

/-- The unit vector at `j`. -/
def uvec {m : ℕ} (j : Fin m) : Fin m → K := fun i => if i = j then 1 else 0

theorem round_uvec {n : ℕ} (w : Fin (4 * n) → K) (j : Fin (4 * n)) (i : ℕ) :
    (AspisR1.RoundPairing.roundPolynomial (uvec j) w).coeff i =
      AspisR1.RoundPairing.quarter * ∑ t : Fin 4,
        (if j.val % 4 + (4 - t.val) % 4 = i then w (AspisR1.childIndex ⟨j.val / 4, by omega⟩ t) else 0) := by
  unfold AspisR1.RoundPairing.roundPolynomial
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  rw [Fintype.sum_eq_single (⟨j.val / 4, by omega⟩ : Fin n) ?_]
  rw [Fintype.sum_eq_single (⟨j.val % 4, by omega⟩ : Fin 4) ?_]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hj : AspisR1.childIndex (⟨j.val / 4, by omega⟩ : Fin n) (⟨j.val % 4, by omega⟩ : Fin 4) = j :=
      Fin.ext (by rw [AspisR1.childIndex_val]; omega)
    rw [hj]
    by_cases hc : j.val % 4 + (4 - t.val) % 4 = i
    · rw [if_pos hc, if_pos hc]
      simp [uvec]
    · rw [if_neg hc, if_neg hc, mul_zero]
  · intro s hs
    apply Finset.sum_eq_zero
    intro t _
    have hne : AspisR1.childIndex (⟨j.val / 4, by omega⟩ : Fin n) s ≠ j := fun h => hs (Fin.ext (by
      have := congrArg Fin.val h
      rw [AspisR1.childIndex_val] at this
      show s.val = j.val % 4
      omega))
    simp [uvec, hne]
  · intro d hd
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro t _
    have hne : AspisR1.childIndex d s ≠ j := fun h => hd (Fin.ext (by
      have := congrArg Fin.val h
      rw [AspisR1.childIndex_val] at this
      show d.val = j.val / 4
      omega))
    simp [uvec, hne]

theorem coefficientFoldValue_sum (α : K) (v : Fin 4 → K) :
    AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue α v = ∑ s : Fin 4, α ^ s.val * v s := by
  have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  unfold AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue
  ring

theorem fold_uvec {n : ℕ} (α : K) (j : Fin (4 * n)) :
    AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer n α (uvec j) =
      α ^ (j.val % 4) • uvec (⟨j.val / 4, by omega⟩ : Fin n) := by
  funext d
  rw [AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer_apply, coefficientFoldValue_sum,
    Pi.smul_apply, smul_eq_mul]
  by_cases hd : d.val = j.val / 4
  · have hd' : d = ⟨j.val / 4, by omega⟩ := Fin.ext hd
    rw [Fintype.sum_eq_single (⟨j.val % 4, by omega⟩ : Fin 4) ?_]
    · have hj : AspisV5ComponentCConcreteFoldLinearity.childIndex d (⟨j.val % 4, by omega⟩ : Fin 4) = j :=
        Fin.ext (by rw [AspisV5ComponentCConcreteFoldLinearity.childIndex_val]; omega)
      simp [uvec, hj, hd']
    · intro s hs
      have hne : AspisV5ComponentCConcreteFoldLinearity.childIndex d s ≠ j := fun h => hs (Fin.ext (by
        have := congrArg Fin.val h
        rw [AspisV5ComponentCConcreteFoldLinearity.childIndex_val] at this
        show s.val = j.val % 4
        omega))
      simp [uvec, hne]
  · have hd' : ¬ d = ⟨j.val / 4, by omega⟩ := fun h => hd (congrArg Fin.val h)
    have hne : ∀ s, AspisV5ComponentCConcreteFoldLinearity.childIndex d s ≠ j := fun s h => hd (by
      have := congrArg Fin.val h
      rw [AspisV5ComponentCConcreteFoldLinearity.childIndex_val] at this
      omega)
    simp [uvec, hne, hd']

theorem exact_uvec (c : K) (d0 : Fin 256) (p : Fin 262144) :
    AspisWide.FinalEncoder.exactFinalLinear (c • uvec d0) p =
      c * naturalLineValue (algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisV7ExactOneFoldDomains.storedFirstLineX18 p)) d0.val := by
  rw [AspisWide.FinalEncoder.exactFinalLinear_apply,
    AspisV5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
  rw [Fintype.sum_eq_single d0 ?_]
  · simp [uvec]
  · intro b hb
    simp [uvec, hb]

/-! ### The batched cells as functionals of the batch -/

/-- Cell `b` of the R1 read as a functional of the γ-batch (Batched `r1Read`). -/
def cellF (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : R1Bat → (InitialMessage K →ₗ[K] K)
  | .round0 i => (Polynomial.lcoeff K i.val).comp (roundPolynomialLinear (n := 256) (weightsR1 π ch))
  | .round1 i => (Polynomial.lcoeff K i.val).comp ((roundPolynomialLinear (n := 64) (w1 π ch)).comp
      (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 (ch.opening 2)))
  | .folded p => if FoldedOpen ch p then (LinearMap.proj p).comp (AspisWide.FinalEncoder.exactFinalLinear.comp
      (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 (ch.opening 2))) else 0
  | .final e => (LinearMap.proj e).comp ((AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64
      (ch.opening 3)).comp (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 (ch.opening 2)))

theorem read_cellF (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (b : R1Bat) :
    BatchedLayer.read (Bat := R1Bat) π ch t b = cellF π ch b (batchR1 π ch t) := by
  cases b with
  | round0 i => rfl
  | round1 i => rfl
  | final e => rfl
  | folded p =>
    by_cases h : FoldedOpen ch p
    · rw [read_folded π ch t p h]
      simp only [cellF, if_pos h]
      rfl
    · rw [folded_unqueried_zero π ch t p h]
      simp only [cellF, if_neg h]
      rfl

theorem batMap_read (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (m : M K F) (b : R1Bat) :
    R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m b =
      BatchedLayer.read (Bat := R1Bat) π ch (pureTrace B m) b := by
  show ((A (Bat := R1Bat) π B ch).comp inlM m) (PayloadCell.bat b) = _
  rw [R0Z.PureRounds.A_pure]
  rfl

theorem batch_gSrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (r : Fin 1024) (k : Fin 4)
    (hr : r ≠ 0) :
    batchR1 π ch (pureTrace B (gSrc (K := K) (F := F) r k)) =
      (ch.opening 0 ^ 27 * R0P.Mask.towerBasis B k) •
        (unitMsg (π r) - (if r ∈ copyInactiveRows then (1 : K) else 0) • unitMsg (π 0)) := by
  have e27 : ((27 : Fin 29) : ℕ) = 27 := rfl
  unfold batchR1
  rw [LinearMap.sum_apply, Fintype.sum_eq_single (27 : Fin 29) ?_]
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, pureTrace_gSrc B r k hr, e27]
    funext j
    obtain ⟨s, rfl⟩ := π.surjective j
    simp only [coeffsLinear_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, unitMsg, balWord,
      Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases h1 : s = r
    · subst h1
      rw [if_pos rfl, if_pos rfl, if_neg hr]
      ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : s = 0
      · subst h2
        rw [if_pos rfl]
        by_cases hm : r ∈ copyInactiveRows
        · rw [if_pos ⟨rfl, hm⟩, if_pos hm]
          ring
        · rw [if_neg (fun h => hm h.2), if_neg hm]
          ring
      · rw [if_neg h2, if_neg (fun h => h2 h.1)]
        ring
  · intro c hc
    rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, pureTrace_gSrc_other B r k c hc,
      map_zero, smul_zero]

/-! ### The unit functional -/

section Unit

variable (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K)
  (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha ch ⟨j, h⟩)
  (hZx : ∀ j : Fin 2, Z (2 * j.val) = (ch.circle j).1.1)
  (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = (ch.circle j).1.2)
  (hT : ∀ r : Fin 1024, T r.val = (π r).val)
  (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
  (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)
  (κ α0 α1 Q : K) (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2) (hα1 : α1 = ch.opening 3)
  (hQ : Q = AspisR1.RoundPairing.quarter)
  {nf : ℕ} (fp : Fin nf → Fin 262144) (X : ℕ → K)
  (hX : ∀ f : Fin nf, X f.val = algebraMap (ZMod AspisCircleGroupOrder.P) K
    (AspisV7ExactOneFoldDomains.storedFirstLineX18 (fp f)))
  (hfo : ∀ f : Fin nf, FoldedOpen ch (fp f))

include hA hZx hZy hT hFl hTI hκ hα0 hα1 hQ hX hfo in
theorem cellF_unit (co : Fin 1024) (c : Fin (78 + nf)) :
    cellF π ch (batCell fp c) (unitMsg co) = ucellP A Z T TI Fl κ α0 α1 Q X nf co.val c.val := by
  have hu : (unitMsg co : InitialMessage K) = uvec (m := 4 * 256) co := rfl
  have hq1 : AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 (ch.opening 2) (unitMsg co) =
      α0 ^ (co.val % 4) • uvec (m := 256) ⟨co.val / 4, by omega⟩ := by
    rw [hu, fold_uvec, hα0]
  unfold batCell ucellP
  by_cases h1 : c.val < 7
  · rw [dif_pos h1, if_pos h1]
    simp only [cellF, LinearMap.comp_apply, Polynomial.lcoeff_apply, roundPolynomialLinear_apply]
    rw [hu, round_uvec (n := 256), hQ,
      ← Fin.sum_univ_eq_sum_range (fun t => if co.val % 4 + (4 - t) % 4 = c.val then
        wtP A Z T TI Fl κ (4 * (co.val / 4) + t) else 0) 4]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hc : co.val % 4 + (4 - t.val) % 4 = c.val
    · rw [if_pos hc, if_pos hc, ← wtP_ident π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ hκ
        (AspisR1.childIndex (⟨co.val / 4, by omega⟩ : Fin 256) t)]
      rfl
    · rw [if_neg hc, if_neg hc]
  rw [dif_neg h1, if_neg h1]
  by_cases h2 : c.val < 14
  · rw [dif_pos h2, if_pos h2]
    simp only [cellF, LinearMap.comp_apply, Polynomial.lcoeff_apply]
    rw [hq1, map_smul, roundPolynomialLinear_apply, Polynomial.coeff_smul, smul_eq_mul,
      round_uvec (n := 64), hQ,
      ← Fin.sum_univ_eq_sum_range (fun t => if co.val / 4 % 4 + (4 - t) % 4 = c.val - 7 then
        w1P A Z T TI Fl κ α0 AspisR1.RoundPairing.quarter (4 * (co.val / 16) + t) else 0) 4]
    congr 2
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hc : co.val / 4 % 4 + (4 - t.val) % 4 = c.val - 7
    · rw [if_pos hc, if_pos hc, ← w1P_ident π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ α0 _ hκ hα0 rfl
        (AspisR1.childIndex (⟨co.val / 4 / 4, by omega⟩ : Fin 64) t)]
      congr 1
      show 4 * (co.val / 4 / 4) + t.val = 4 * (co.val / 16) + t.val
      omega
    · rw [if_neg hc, if_neg hc]
  rw [dif_neg h2, if_neg h2]
  by_cases h3 : c.val < 14 + nf
  · rw [dif_pos h3, if_pos h3]
    have ho := hfo ⟨c.val - 14, by omega⟩
    simp only [cellF, if_pos ho, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hq1, exact_uvec, hX ⟨c.val - 14, by omega⟩,
      natP_eq _ 8 (co.val / 4) (by have := co.isLt; norm_num; omega)]
  · rw [dif_neg h3, if_neg h3]
    simp only [cellF, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hq1, map_smul, Pi.smul_apply, smul_eq_mul, fold_uvec, Pi.smul_apply, smul_eq_mul, ← hα1]
    simp only [uvec, Fin.ext_iff]
    by_cases he : c.val - 14 - nf = co.val / 4 / 4
    · rw [if_pos he, if_pos (show c.val - (14 + nf) = co.val / 16 by omega)]
      ring
    · rw [if_neg he, if_neg (show ¬ c.val - (14 + nf) = co.val / 16 by omega)]
      ring

end Unit

theorem towerBasis_tbP (B : PackBasis F) (k : Fin 4) : R0P.Mask.towerBasis B k = tbP B.i B.u k.val := by
  fin_cases k <;> rfl

/-- **`gbat_cell`**: every support cell of a G source's batched image is the model `gbatP`. -/
theorem gbat_cell (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (A Z : ℕ → K) (T TI : ℕ → ℕ)
    (Fl : ℕ → K)
    (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha ch ⟨j, h⟩)
    (hZx : ∀ j : Fin 2, Z (2 * j.val) = (ch.circle j).1.1)
    (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = (ch.circle j).1.2)
    (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)
    (γ κ α0 α1 Q : K) (hγ : γ = ch.opening 0) (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2)
    (hα1 : α1 = ch.opening 3) (hQ : Q = AspisR1.RoundPairing.quarter)
    {nf : ℕ} (fp : Fin nf → Fin 262144) (X : ℕ → K)
    (hX : ∀ f : Fin nf, X f.val = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV7ExactOneFoldDomains.storedFirstLineX18 (fp f)))
    (hfo : ∀ f : Fin nf, FoldedOpen ch (fp f))
    (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) (c : Fin (78 + nf)) :
    R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch (gSrc (K := K) (F := F) r k) (batCell fp c) =
      gbatP A Z T TI Fl γ κ α0 α1 Q B.i B.u X nf r.val k.val c.val := by
  have hT0 : T 0 = (π 0).val := by
    have := hT 0
    rwa [Fin.val_zero] at this
  rw [batMap_read, read_cellF, batch_gSrc π B ch r k hr, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul,
    cellF_unit π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ α0 α1 Q hκ hα0 hα1 hQ fp X hX hfo,
    cellF_unit π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ α0 α1 Q hκ hα0 hα1 hQ fp X hX hfo]
  unfold gbatP
  rw [hT r, hT0, hFl r, towerBasis_tbP, hγ]

/-- **`gbat_ident`**: the `hGBat` shape from the column entry premise. -/
theorem gbat_ident (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (A Z : ℕ → K) (T TI : ℕ → ℕ)
    (Fl : ℕ → K)
    (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha ch ⟨j, h⟩)
    (hZx : ∀ j : Fin 2, Z (2 * j.val) = (ch.circle j).1.1)
    (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = (ch.circle j).1.2)
    (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)
    (γ κ α0 α1 Q : K) (hγ : γ = ch.opening 0) (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2)
    (hα1 : α1 = ch.opening 3) (hQ : Q = AspisR1.RoundPairing.quarter)
    (wb : Module.Basis (Fin 8) F K) {nf : ℕ} (fp : Fin nf → Fin 262144) (X : ℕ → K)
    (hX : ∀ f : Fin nf, X f.val = algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV7ExactOneFoldDomains.storedFirstLineX18 (fp f)))
    (hfo : ∀ f : Fin nf, FoldedOpen ch (fp f))
    (φ : R1Z.CertData.ZP →+* ↥F) {NG : ℕ} (sel : Fin NG → Fin 1024 × Fin 4) (hsel0 : ∀ t, (sel t).1 ≠ 0)
    (m : ℕ → R1Z.CertData.ZP) (s : ℕ)
    (hent : ∀ (t : Fin NG) (c : Fin (78 + nf)),
      ∑ l : Fin 8, φ (m (t.val * s + (8 * c.val + l.val))) • wb l =
        gbatP A Z T TI Fl γ κ α0 α1 Q B.i B.u X nf (sel t).1.val (sel t).2.val c.val) :
    ∀ (i : Fin ((78 + nf) * 8)) (t : Fin NG),
      flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch (gSrc (sel t).1 (sel t).2)) i =
        φ (R1Z.CertData.colM m s i t) := by
  intro i t
  have hi : 8 * ((fpb nf).symm i).1.val + ((fpb nf).symm i).2.val = i.val := by
    have e := congrArg Fin.val ((fpb nf).apply_symm_apply i)
    have hv : ∀ (c : Fin (78 + nf)) (l : Fin 8), (fpb nf (c, l)).val = l.val + 8 * c.val := by
      intro c l
      simp [fpb, finProdFinEquiv]
    rw [hv] at e
    omega
  unfold flatB R1Z.CertData.colM
  rw [gbat_cell π B ch A Z T TI Fl hA hZx hZy hT hFl hTI γ κ α0 α1 Q hγ hκ hα0 hα1 hQ fp X hX hfo
    _ _ (hsel0 t), ← hent t, wb.repr_sum_self]
  simp only [hi]

#print axioms round_uvec
#print axioms fold_uvec
#print axioms exact_uvec
#print axioms read_cellF
#print axioms batMap_read
#print axioms batch_gSrc
#print axioms cellF_unit
#print axioms gbat_cell
#print axioms gbat_ident

end R1Z.CertRel

end
