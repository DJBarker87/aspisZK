import R0Z.SilentReduction
import R1Z.CertSound

/-! D49.4 C2: RF-chain (proved) and the reduction of RF-round to its coordinate
closed form (zf1/DESIGN-P-CERT.txt §1.4, §2.3), Lean side.

**The Z4c round coordinates** (z4/probe.rs:262-337 `round_row`, 1834-1846
`last_coeff`).  A round payload `t : Fin 10 → Fin 28 → K` has 271 coordinates
`z4c t`: entry 0 is the initial sum `p₀(0) + p₀(1)`; entry `1 + 27j` is the
constant coefficient of round `j`; entry `1 + 27j + k` (`1 ≤ k ≤ 26`) is its
coefficient `k + 1`.  The linear coefficients are dropped.  `recon a v`
rebuilds them as `last_coeff` does: `c₁ = prev − 2c₀ − Σ_{d≥2} c_d`, with
`prev` the initial sum for round 0 and the previous round at `α_{j-1}`
afterwards.  The checker's round space is `F^1084`, four tower limbs per
coordinate in `flatten` order `4p + k`; `iotaR B a = recon a ∘ unflat`.

**RF-chain.**  `chainTarget i = flatten(normalize_d(unflat e_i, final(unflat e_i)))`
(z9c.rs:208-219 `chain_targets`; probe.rs:2279-2297 `final_value`,
`normalize_d`).  `rf_chain`: if every α lies in `K₄` (`SemK4`), then
`ChainT0K4 ≤ span_F {iotaR (chainTarget i)}` — exactly the `rf_chain` premise
of `CertR1.qprime_of_cert` with `ιr = iotaR`, `T = chainTarget`.  It needs no
`HalfOK`: for a terminal-zero vector `normalize_d` is the identity whatever
inverse is used.

**RF-round, reduced.**  `roundMaskMap_recon`: every round image of a mask tape
satisfies the nine chain equalities, so `recon ∘ z4c` is the identity on it.
Hence (`rf_round_of_coords`) the `rf_round` premise with `ιr = iotaR` follows
from the coordinate identity `z4c (roundMaskMap (src t)) = unflat (col Rnd t)`,
i.e. from the closed form of the 271 K-valued Z4c coordinates of each source
(the Rust `round_row` / `tail_row`), which remains open.

Nothing here evaluates a sum over the Boolean cube, the 1,084 coordinates or
the 1,024 rows. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfChain

open scoped BigOperators
open R0P R0Z.HonestView R0Z.K4 R0Z.SilentReduction R0Z.Partition R0Z.D12 Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Round evaluation and the Z4c coordinates -/

/-- Evaluation of a 28-coefficient round. -/
def pev (c : Fin 28 → K) (x : K) : K := ∑ i : Fin 28, c i * x ^ i.val

theorem pev_zero (c : Fin 28 → K) : pev c 0 = c 0 := by
  unfold pev
  rw [Fin.sum_univ_succ]
  simp

theorem pev_one (c : Fin 28 → K) : pev c 1 = ∑ i : Fin 28, c i := by
  simp [pev]

theorem pev_add (c d : Fin 28 → K) (x : K) : pev (c + d) x = pev c x + pev d x := by
  simp only [pev, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pev_smul (s : K) (c : Fin 28 → K) (x : K) : pev (s • c) x = s * pev c x := by
  simp only [pev, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sum28 (c : Fin 28 → K) :
    ∑ i : Fin 28, c i = c 0 + c 1 + ∑ k : Fin 26, c k.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  exact (add_assoc _ _ _).symm

/-- Z4c index of round `j`, entry `k` (probe.rs:322-328: `out.push(full[0])`,
`out.extend(&full[2..])`). -/
def idx (j : Fin 10) (k : Fin 27) : Fin 271 := ⟨1 + 27 * j.val + k.val, by omega⟩

/-- The round coefficient stored at entry `k`. -/
def coeffOf (k : Fin 27) : Fin 28 := if k.val = 0 then 0 else ⟨k.val + 1, by omega⟩

theorem coeffOf_zero : coeffOf 0 = 0 := by
  unfold coeffOf
  exact if_pos rfl

theorem coeffOf_succ (k : Fin 26) : coeffOf k.succ = k.succ.succ := by
  unfold coeffOf
  rw [if_neg (by simp only [Fin.val_succ]; omega)]
  apply Fin.ext
  simp only [Fin.val_succ]

/-- The Z4c coordinates of a round payload. -/
def z4c (t : R0Z.PayloadSplit.RoundPayload K) (p : Fin 271) : K :=
  if p.val = 0 then pev (t 0) 0 + pev (t 0) 1
  else t ⟨(p.val - 1) / 27, by omega⟩ (coeffOf ⟨(p.val - 1) % 27, by omega⟩)

theorem z4c_zero (t : R0Z.PayloadSplit.RoundPayload K) :
    z4c t 0 = pev (t 0) 0 + pev (t 0) 1 := by
  unfold z4c
  exact if_pos rfl

theorem z4c_idx (t : R0Z.PayloadSplit.RoundPayload K) (j : Fin 10) (k : Fin 27) :
    z4c t (idx j k) = t j (coeffOf k) := by
  have hj := j.isLt
  have hk := k.isLt
  have h0 : (idx j k).val ≠ 0 := by simp only [idx]; omega
  have ej : ((idx j k).val - 1) / 27 = j.val := by simp only [idx]; omega
  have ek : ((idx j k).val - 1) % 27 = k.val := by simp only [idx]; omega
  unfold z4c
  rw [if_neg h0]
  congr <;> first | exact Fin.ext ej | exact Fin.ext ek

/-! ### Reconstruction (Rust `last_coeff`) -/

/-- Round `j` from its Z4c entries and its boundary target `prev`. -/
def reconRound (v : Fin 271 → K) (j : Fin 10) (prev : K) : Fin 28 → K := fun d =>
  if d.val = 0 then v (idx j 0)
  else if d.val = 1 then prev - (v (idx j 0) + v (idx j 0)) - ∑ k : Fin 26, v (idx j k.succ)
  else v (idx j ⟨d.val - 1, by omega⟩)

/-- The boundary target of round `n` (`prev` in `last_coeff`). -/
def prevAt (a : Fin 10 → K) (v : Fin 271 → K) : ℕ → K
  | 0 => v 0
  | n + 1 => if h : n < 10 then pev (reconRound v ⟨n, h⟩ (prevAt a v n)) (a ⟨n, h⟩) else 0

/-- The rebuilt round payload. -/
def recon (a : Fin 10 → K) (v : Fin 271 → K) : R0Z.PayloadSplit.RoundPayload K :=
  fun j => reconRound v j (prevAt a v j.val)

theorem reconRound_add (v w : Fin 271 → K) (j : Fin 10) (p q : K) :
    reconRound (v + w) j (p + q) = reconRound v j p + reconRound w j q := by
  funext d
  simp only [reconRound, Pi.add_apply, Finset.sum_add_distrib]
  split_ifs <;> ring

theorem reconRound_smul (s : K) (v : Fin 271 → K) (j : Fin 10) (p : K) :
    reconRound (s • v) j (s * p) = s • reconRound v j p := by
  funext d
  simp only [reconRound, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

theorem prevAt_add (a : Fin 10 → K) (v w : Fin 271 → K) :
    ∀ n, prevAt a (v + w) n = prevAt a v n + prevAt a w n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prevAt]
    by_cases h : n < 10
    · rw [dif_pos h, dif_pos h, dif_pos h, ih, reconRound_add, pev_add]
    · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem prevAt_smul (a : Fin 10 → K) (s : K) (v : Fin 271 → K) :
    ∀ n, prevAt a (s • v) n = s * prevAt a v n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prevAt]
    by_cases h : n < 10
    · rw [dif_pos h, dif_pos h, ih, reconRound_smul, pev_smul]
    · rw [dif_neg h, dif_neg h, mul_zero]

/-- `recon a` as a `K`-linear map. -/
def reconL (a : Fin 10 → K) : (Fin 271 → K) →ₗ[K] R0Z.PayloadSplit.RoundPayload K where
  toFun := recon a
  map_add' v w := by
    funext j
    simp only [recon, Pi.add_apply]
    rw [prevAt_add, reconRound_add]
  map_smul' s v := by
    funext j
    simp only [recon, Pi.smul_apply, RingHom.id_apply]
    rw [prevAt_smul, reconRound_smul]

theorem reconL_apply (a : Fin 10 → K) (v : Fin 271 → K) : reconL a v = recon a v := rfl

/-- `last_coeff` inverts the Z4c coordinates on round payloads with the nine
chain equalities. -/
theorem reconRound_z4c (t : R0Z.PayloadSplit.RoundPayload K) (j : Fin 10) :
    reconRound (z4c t) j (pev (t j) 0 + pev (t j) 1) = t j := by
  funext d
  unfold reconRound
  by_cases h0 : d.val = 0
  · rw [if_pos h0, z4c_idx, coeffOf_zero]
    exact congrArg (t j) (Fin.ext h0).symm
  · rw [if_neg h0]
    by_cases h1 : d.val = 1
    · rw [if_pos h1]
      have hd : d = 1 := Fin.ext h1
      rw [hd, pev_zero, pev_one, sum28]
      simp only [z4c_idx, coeffOf_zero, coeffOf_succ]
      ring
    · rw [if_neg h1, z4c_idx]
      congr 1
      unfold coeffOf
      rw [if_neg (by simp only; omega)]
      apply Fin.ext
      simp only
      omega

theorem prevAt_z4c (a : Fin 10 → K) (t : R0Z.PayloadSplit.RoundPayload K)
    (hchain : ∀ j : Fin 9, pev (t j.succ) 0 + pev (t j.succ) 1 = pev (t j.castSucc) (a j.castSucc)) :
    ∀ n (hn : n < 10), prevAt a (z4c t) n = pev (t ⟨n, hn⟩) 0 + pev (t ⟨n, hn⟩) 1 := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact z4c_zero t
  | succ n ih =>
    intro hn
    have hn' : n < 10 := by omega
    simp only [prevAt]
    rw [dif_pos hn', ih hn', reconRound_z4c]
    exact (hchain ⟨n, by omega⟩).symm

/-- `recon ∘ z4c = id` on the chain. -/
theorem recon_z4c (a : Fin 10 → K) (t : R0Z.PayloadSplit.RoundPayload K)
    (hchain : ∀ j : Fin 9, pev (t j.succ) 0 + pev (t j.succ) 1 = pev (t j.castSucc) (a j.castSucc)) :
    recon a (z4c t) = t := by
  funext j
  unfold recon
  rw [prevAt_z4c a t hchain j.val j.isLt]
  exact reconRound_z4c t j

/-! ### `final_value` and `normalize_d` -/

/-- Rust `final_value`: the last rebuilt round at `α₉`. -/
def finalVal (a : Fin 10 → K) (v : Fin 271 → K) : K := pev (recon a v 9) (a 9)

theorem finalVal_add (a : Fin 10 → K) (v w : Fin 271 → K) :
    finalVal a (v + w) = finalVal a v + finalVal a w := by
  show pev (reconL a (v + w) 9) (a 9) = pev (reconL a v 9) (a 9) + pev (reconL a w 9) (a 9)
  rw [map_add, Pi.add_apply, pev_add]

theorem finalVal_smul (a : Fin 10 → K) (s : K) (v : Fin 271 → K) :
    finalVal a (s • v) = s * finalVal a v := by
  show pev (reconL a (s • v) 9) (a 9) = s * pev (reconL a v 9) (a 9)
  rw [map_smul, Pi.smul_apply, pev_smul]

/-- The `normalize_d` factor `(α₉ − ½)⁻¹ · ½`. -/
def corr (a : Fin 10 → K) : K := (a 9 - 1 / 2)⁻¹ * (1 / 2)

/-- Rust `normalize_d(v, final_value(v))`: entry 244 = `idx 9 0` gains
`φ·(α₉ − ½)⁻¹·½`. -/
def normalize (a : Fin 10 → K) (v : Fin 271 → K) : Fin 271 → K :=
  v + (finalVal a v * corr a) • Pi.single (idx 9 0) 1

theorem idx_nine_zero : (idx 9 0).val = 244 := rfl

/-- `normalize` as a `K`-linear map. -/
def normL (a : Fin 10 → K) : (Fin 271 → K) →ₗ[K] (Fin 271 → K) where
  toFun := normalize a
  map_add' v w := by
    simp only [normalize, finalVal_add, add_mul, add_smul]
    abel
  map_smul' s v := by
    simp only [normalize, finalVal_smul, RingHom.id_apply, smul_add, smul_smul, mul_assoc]

theorem normalize_of_final (a : Fin 10 → K) (v : Fin 271 → K) (h : finalVal a v = 0) :
    normalize a v = v := by
  simp only [normalize, h, zero_mul, zero_smul, add_zero]

/-! ### Limbs: `unflat` and `flatten` -/

/-- `flatten` order: limb `k` of coordinate `p` is index `4p + k`. -/
def fpe : Fin 271 × Fin 4 ≃ Fin 1084 := finProdFinEquiv

/-- Rust `unflat` (z8.rs:97): four tower limbs to a QM31 value (`pack4`). -/
def unflatL (B : PackBasis F) : (Fin 1084 → F) →ₗ[F] (Fin 271 → K) where
  toFun x p := pack4 B (fun k => (x (fpe (p, k)) : K))
  map_add' x y := by
    funext p
    simp only [pack4, Pi.add_apply, Subfield.coe_add]
    ring
  map_smul' c x := by
    funext p
    simp only [pack4, Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply, fsmul_eq]
    ring

theorem unflatL_apply (B : PackBasis F) (x : Fin 1084 → F) (p : Fin 271) :
    unflatL B x p = pack4 B (fun k => (x (fpe (p, k)) : K)) := rfl

/-- The tower limbs of a `K₄` element (its unique `pack4` coordinates). -/
def limbs (B : PackBasis F) (hB : PackField B) (x : K) : Fin 4 → F :=
  if h : x ∈ K4 B hB then
    fun j => ⟨Classical.choose ((mem_K4_iff_pack4 B hB).1 h) j,
      (Classical.choose_spec ((mem_K4_iff_pack4 B hB).1 h)).1 j⟩
  else 0

theorem pack4_limbs (B : PackBasis F) (hB : PackField B) {x : K} (hx : x ∈ K4 B hB) :
    pack4 B (fun j => (limbs B hB x j : K)) = x := by
  unfold limbs
  rw [dif_pos hx]
  exact (Classical.choose_spec ((mem_K4_iff_pack4 B hB).1 hx)).2.symm

/-- Rust `flatten`: the 1,084 tower limbs of 271 `K₄` values. -/
def flat (B : PackBasis F) (hB : PackField B) (w : Fin 271 → K) : Fin 1084 → F :=
  fun i => limbs B hB (w (fpe.symm i).1) (fpe.symm i).2

theorem unflat_flat (B : PackBasis F) (hB : PackField B) (w : Fin 271 → K)
    (hw : ∀ p, w p ∈ K4 B hB) : unflatL B (flat B hB w) = w := by
  funext p
  rw [unflatL_apply]
  simp only [flat, Equiv.symm_apply_apply]
  exact pack4_limbs B hB (hw p)

/-! ### Membership in `K₄` -/

section Mem

variable (B : PackBasis F) (hB : PackField B)

theorem pev_mem {c : Fin 28 → K} {x : K} (hc : ∀ i, c i ∈ K4 B hB) (hx : x ∈ K4 B hB) :
    pev c x ∈ K4 B hB :=
  sum_mem (fun i _ => (K4 B hB).mul_mem (hc i) ((K4 B hB).pow_mem hx _))

theorem reconRound_mem {v : Fin 271 → K} {p : K} (j : Fin 10) (hv : ∀ q, v q ∈ K4 B hB)
    (hp : p ∈ K4 B hB) (d : Fin 28) : reconRound v j p d ∈ K4 B hB := by
  unfold reconRound
  split_ifs
  · exact hv _
  · exact (K4 B hB).sub_mem ((K4 B hB).sub_mem hp ((K4 B hB).add_mem (hv _) (hv _)))
      (sum_mem (fun k _ => hv _))
  · exact hv _

theorem prevAt_mem {a : Fin 10 → K} {v : Fin 271 → K} (ha : ∀ j, a j ∈ K4 B hB)
    (hv : ∀ q, v q ∈ K4 B hB) : ∀ n, prevAt a v n ∈ K4 B hB := by
  intro n
  induction n with
  | zero => exact hv 0
  | succ n ih =>
    simp only [prevAt]
    by_cases h : n < 10
    · rw [dif_pos h]
      exact pev_mem B hB (reconRound_mem B hB _ hv ih) (ha _)
    · rw [dif_neg h]
      exact (K4 B hB).zero_mem

theorem recon_mem {a : Fin 10 → K} {v : Fin 271 → K} (ha : ∀ j, a j ∈ K4 B hB)
    (hv : ∀ q, v q ∈ K4 B hB) (j : Fin 10) (d : Fin 28) : recon a v j d ∈ K4 B hB :=
  reconRound_mem B hB j hv (prevAt_mem B hB ha hv _) d

theorem normalize_mem {a : Fin 10 → K} {v : Fin 271 → K} (ha : ∀ j, a j ∈ K4 B hB)
    (hv : ∀ q, v q ∈ K4 B hB) (q : Fin 271) : normalize a v q ∈ K4 B hB := by
  have hf : finalVal a v ∈ K4 B hB := pev_mem B hB (fun d => recon_mem B hB ha hv 9 d) (ha 9)
  have hc : corr a ∈ K4 B hB :=
    (K4 B hB).mul_mem ((K4 B hB).inv_mem ((K4 B hB).sub_mem (ha 9) (half_mem_K4 B hB)))
      (half_mem_K4 B hB)
  have hs : (Pi.single (idx 9 0) (1 : K) : Fin 271 → K) q ∈ K4 B hB := by
    rw [Pi.single_apply]
    split_ifs
    · exact (K4 B hB).one_mem
    · exact (K4 B hB).zero_mem
  simp only [normalize, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (K4 B hB).add_mem (hv q) ((K4 B hB).mul_mem ((K4 B hB).mul_mem hf hc) hs)

theorem unflat_mem (x : Fin 1084 → F) (q : Fin 271) : unflatL B x q ∈ K4 B hB :=
  (mem_K4_iff_pack4 B hB).2 ⟨fun k => (x (fpe (q, k)) : K), fun k => (x (fpe (q, k))).2, rfl⟩

theorem z4c_mem {t : R0Z.PayloadSplit.RoundPayload K} (ht : ∀ j i, t j i ∈ K4 B hB)
    (q : Fin 271) : z4c t q ∈ K4 B hB := by
  unfold z4c
  split_ifs
  · exact (K4 B hB).add_mem (pev_mem B hB (ht 0) (K4 B hB).zero_mem)
      (pev_mem B hB (ht 0) (K4 B hB).one_mem)
  · exact ht _ _

end Mem

/-! ### RF-chain -/

/-- The checker's round coordinate embedding `ιr`. -/
def iotaR (B : PackBasis F) (a : Fin 10 → K) :
    (Fin 1084 → F) →ₗ[F] R0Z.PayloadSplit.RoundPayload K :=
  ((reconL a).restrictScalars F).comp (unflatL B)

theorem iotaR_apply (B : PackBasis F) (a : Fin 10 → K) (x : Fin 1084 → F) :
    iotaR B a x = recon a (unflatL B x) := rfl

/-- The checker's `ChainT0K4` generators (z9c.rs:208-219 `chain_targets`):
`flatten(normalize_d(unflat e_i, final_value(unflat e_i)))`. -/
def chainTarget (B : PackBasis F) (hB : PackField B) (a : Fin 10 → K) (i : Fin 1084) :
    Fin 1084 → F :=
  flat B hB (normalize a (unflatL B (fun j => if i = j then (1 : F) else 0)))

theorem vec_decomp (x : Fin 1084 → F) :
    x = ∑ i, x i • (fun j => if i = j then (1 : F) else 0) := by
  funext j
  rw [Finset.sum_apply]
  simp [Finset.sum_ite_eq']

variable {Bat : Type} [BatchedLayer K Bat]

theorem eval_roundInclusion (t : R0Z.PayloadSplit.RoundPayload K) (j : Fin 10) (x : K) :
    (R0Z.Chain.roundPoly (Bat := Bat) j (R0Z.PayloadSplit.roundInclusion (Bat := Bat) t)).eval x =
      pev (t j) x := by
  rw [R0Z.Chain.roundPoly_apply, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, pev]
  rfl

/-- **RF-chain.**  Under `SemK4` (every α in `K₄`), `ChainT0K4` lies in the
`F`-span of the checker's normalised generators, through `ιr = iotaR`. -/
theorem rf_chain (B : PackBasis F) (hB : PackField B) (ch : Challenges K)
    (ha : ∀ j, alpha ch j ∈ K4 B hB) :
    ChainT0K4 (Bat := Bat) B hB ch ≤
      Submodule.span F (Set.range fun i => iotaR B (alpha ch) (chainTarget B hB (alpha ch) i)) := by
  intro t ht
  rcases Submodule.mem_inf.1 ht with ⟨hc, hk⟩
  have hc' : t ∈ ChainT0 (Bat := Bat) ch := hc
  rw [mem_chainT0_iff] at hc'
  obtain ⟨hch, hterm⟩ := hc'
  have hk' := (mem_K4Round_iff B hB t).1 hk
  have hchain : ∀ j : Fin 9, pev (t j.succ) 0 + pev (t j.succ) 1 =
      pev (t j.castSucc) (alpha ch j.castSucc) := by
    intro j
    have h := hch j
    rw [eval_roundInclusion (Bat := Bat), eval_roundInclusion (Bat := Bat),
      eval_roundInclusion (Bat := Bat)] at h
    exact h
  have hrec : recon (alpha ch) (z4c t) = t := recon_z4c (alpha ch) t hchain
  have hfin : finalVal (alpha ch) (z4c t) = 0 := by
    have h9 := hterm
    rw [eval_roundInclusion (Bat := Bat)] at h9
    unfold finalVal
    rw [hrec]
    exact h9
  have hv : ∀ q, z4c t q ∈ K4 B hB := z4c_mem B hB hk'
  let Φ : (Fin 271 → K) →ₗ[F] R0Z.PayloadSplit.RoundPayload K :=
    ((reconL (alpha ch)).comp (normL (alpha ch))).restrictScalars F
  have hΦ : ∀ v, Φ v = recon (alpha ch) (normalize (alpha ch) v) := fun v => rfl
  have hdec : z4c t = ∑ i, (flat B hB (z4c t) i) •
      unflatL B (fun j => if i = j then (1 : F) else 0) := by
    calc z4c t = unflatL B (flat B hB (z4c t)) := (unflat_flat B hB (z4c t) hv).symm
      _ = unflatL B (∑ i, flat B hB (z4c t) i • fun j => if i = j then (1 : F) else 0) :=
          congrArg (unflatL B) (vec_decomp _)
      _ = ∑ i, (flat B hB (z4c t) i) • unflatL B (fun j => if i = j then (1 : F) else 0) := by
          rw [map_sum]
          simp only [map_smul]
  have hgen : ∀ i, Φ (unflatL B (fun j => if i = j then (1 : F) else 0)) =
      iotaR B (alpha ch) (chainTarget B hB (alpha ch) i) := by
    intro i
    rw [hΦ, iotaR_apply, chainTarget, unflat_flat B hB _
      (normalize_mem B hB ha (unflat_mem B hB _))]
  have heq : t = ∑ i, (flat B hB (z4c t) i) • iotaR B (alpha ch) (chainTarget B hB (alpha ch) i) := by
    calc t = recon (alpha ch) (normalize (alpha ch) (z4c t)) := by
          rw [normalize_of_final _ _ hfin, hrec]
      _ = Φ (z4c t) := (hΦ _).symm
      _ = _ := by
          conv_lhs => rw [hdec]
          rw [map_sum]
          simp only [map_smul, hgen]
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-! ### RF-round, reduced to the coordinate closed form -/

/-- Round `j` of a payload, evaluated. -/
theorem eval_payload (v : Payload K Bat) (j : Fin 10) (x : K) :
    (R0Z.Chain.roundPoly (Bat := Bat) j v).eval x = pev (fun i => v (.semanticCoeff j i)) x := by
  rw [R0Z.Chain.roundPoly_apply, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, pev]

theorem roundMaskMap_apply (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) (j : Fin 10) (i : Fin 28) :
    R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j i =
      (A (Bat := Bat) π B ch).comp inlM m (.semanticCoeff j i) := by
  simp only [R0Z.Z4Maps.roundMaskMap, R0Z.Z4Maps.roundProjection, LinearMap.comp_apply,
    LinearMap.pi_apply, LinearMap.proj_apply]

/-- Round images of mask tapes satisfy the nine chain equalities. -/
theorem roundMaskMap_chain (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) (j : Fin 9) :
    pev (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j.succ) 0 +
        pev (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j.succ) 1 =
      pev (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j.castSucc) (alpha ch j.castSucc) := by
  have e : ∀ (k : Fin 10) (x : K), pev (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m k) x =
      (R0Z.Chain.roundPoly (Bat := Bat) k ((A (Bat := Bat) π B ch).comp inlM m)).eval x :=
    fun k x => by
      rw [eval_payload]
      simp only [pev, roundMaskMap_apply]
  rw [e, e, e, R0Z.PureRounds.A_pure, R0Z.PureRounds.roundPoly_L, R0Z.PureRounds.roundPoly_L]
  exact R0Z.Chain.rounds_chain ch _ (R0Z.Shift.maskLinear_vdeg π B _) j

/-- `recon ∘ z4c` is the identity on round images of mask tapes. -/
theorem roundMaskMap_recon (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) :
    recon (alpha ch) (z4c (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m)) =
      R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m :=
  recon_z4c _ _ (roundMaskMap_chain π B ch m)

/-- **RF-round from its coordinate closed form.**  If the Z4c coordinates of
each source's round image are the `unflat` of the checker's column, then the
`rf_round` premise of `CertR1.qprime_of_cert` / `bcondG_of_cert` holds with
`ιr = iotaR`. -/
theorem rf_round_of_coords (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    {N : ℕ} (src : Fin N → M K F) (Rnd : Fin 1084 → Fin N → F)
    (h : ∀ t, z4c (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (src t)) =
      unflatL B (R1Z.CertSound.col Rnd t)) :
    ∀ t, R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (src t) =
      iotaR B (alpha ch) (R1Z.CertSound.col Rnd t) := by
  intro t
  rw [← roundMaskMap_recon π B ch (src t), h t]
  rfl

#print axioms pev_zero
#print axioms sum28
#print axioms z4c_idx
#print axioms prevAt_add
#print axioms prevAt_smul
#print axioms reconRound_z4c
#print axioms prevAt_z4c
#print axioms recon_z4c
#print axioms finalVal_add
#print axioms normalize_of_final
#print axioms unflat_flat
#print axioms normalize_mem
#print axioms z4c_mem
#print axioms vec_decomp
#print axioms eval_roundInclusion
#print axioms rf_chain
#print axioms eval_payload
#print axioms roundMaskMap_apply
#print axioms roundMaskMap_chain
#print axioms roundMaskMap_recon
#print axioms rf_round_of_coords

end R1Z.RfChain

end
