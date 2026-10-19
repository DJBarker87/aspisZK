import R1Z.PredicateR1
import R1Z.RfOwn
import R1Z.RfChain

/-! D49.4 C2: RF-obs and RF-col for the (ii′) lifts (zf1/DESIGN-P-CERT.txt
§1.6, §2.3), Lean side.

**Coordinates.**  The checker's lift coordinates are those of z9c.rs:224-246
(`lift_src`): the C1 lanes use `raw_c`'s base row without its inactive
indicator (probe.rs:2223-2251: claims 3×4 limbs, extra 4, OOD 2×4, then one base
limb per query and slot, width `24 + 4n`, 112 at n = 22); the H1 lane uses the
QM31 row flattened (four limbs for every value, width `24 + 16n`, 376 at
n = 22).  `iotaC1 l` / `iotaH1 l` assemble an own-cell vector from those limbs
for the query list `l` (an opened cell reads any list position holding its
query, so repeated queries are harmless).

**RF-obs** (`rf_obs_C1`, `rf_obs_H1`): if the query set is `l.toFinset`, every
α and both circle points lie in `K₄`, then the own observations of base-field
(resp. `K₄`-valued) lane words are in the range of `iotaC1` (resp. `iotaH1`).
The inactive-sum condition of `Wsem`/`Wh1` is not needed.

**RF-col** (`rf_col_C1`, `rf_col_H1`): with the column matrix
`O i t = flat(obs(src t)) i` the `rf_col` premise holds for the lift sources
`c1Src`, `h1Src`.  `obs_balWord_*` give the closed form of those columns (the
Rust `eq`/`h_weight`/`evalrow` values of `raw_c`, differenced against the
dependent row), which is what the C3 extraction must match. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfObs

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.K4
open AspisR0.Opening AspisR0.ChordGeometry AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.Agreement AspisCircleTensorBinding
open R1Z.PredicateR1 R1Z.RfSrc R1Z.RfOwn R1Z.RfChain

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Membership facts -/

theorem algebraMap_mem (S : Subfield K) (z : ZMod AspisCircleGroupOrder.P) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K z ∈ S := by
  rw [← ZMod.natCast_zmod_val z, map_natCast]
  exact natCast_mem S _

theorem doubledFactor_mem (S : Subfield K) {x : K} (hx : x ∈ S) : ∀ b, doubledFactor x b ∈ S
  | 0 => hx
  | b + 1 => by
    have h2 : (2 : K) ∈ S := by simpa using natCast_mem S 2
    rw [doubledFactor]
    exact S.sub_mem (S.mul_mem h2 (S.pow_mem (doubledFactor_mem S hx b) 2)) S.one_mem

theorem naturalLineValue_mem (S : Subfield K) {x : K} (hx : x ∈ S) (n : ℕ) :
    naturalLineValue x n ∈ S :=
  prod_mem (fun b _ => doubledFactor_mem S hx b)

theorem rustEvalRow_mem (S : Subfield K) (co : Fin 1024) {x y : K} (hx : x ∈ S) (hy : y ∈ S) :
    rustEvalRow co x y ∈ S := by
  unfold rustEvalRow
  split_ifs
  · exact naturalLineValue_mem S hx _
  · exact S.mul_mem (naturalLineValue_mem S hx _) hy

theorem succCarry_mem (S : Subfield K) {p : Fin 10 → K} (hp : ∀ b, p b ∈ S) :
    ∀ k, succCarry p k ∈ S
  | 0 => S.one_mem
  | k + 1 => by
    rw [succCarry]
    refine S.mul_mem ?_ (succCarry_mem S hp k)
    split_ifs
    · exact hp _
    · exact S.zero_mem

theorem openingPoints_mem (S : Subfield K) {a : Fin 10 → K} (ha : ∀ j, a j ∈ S)
    (j : Fin 3) (b : Fin 10) : openingPoints a j b ∈ S := by
  rw [openingPoints_eq]
  unfold toR0
  fin_cases j
  · exact ha _
  · show successorPoint a _ ∈ S
    unfold successorPoint
    have hc := succCarry_mem S ha (9 - (⟨9 - b.val, by omega⟩ : Fin 10).val)
    exact S.sub_mem (S.add_mem (ha _) hc) (S.add_mem (S.mul_mem (ha _) hc) (S.mul_mem (ha _) hc))
  · show xor12Point a _ ∈ S
    unfold xor12Point
    split_ifs
    · exact S.sub_mem S.one_mem (ha _)
    · exact ha _

theorem eqWeight_mem (S : Subfield K) {p : Fin 10 → K} (hp : ∀ b, p b ∈ S) (r : Fin 1024) :
    eqWeight p r ∈ S := by
  unfold eqWeight
  refine prod_mem (fun b _ => ?_)
  split_ifs
  · exact S.sub_mem S.one_mem (hp b)
  · exact hp b

theorem libraWeight_mem (S : Subfield K) {a : Fin 10 → K} (ha : ∀ j, a j ∈ S) (i : Fin 1024) :
    libraWeight a i ∈ S := by
  unfold libraWeight
  split_ifs
  · exact S.pow_mem (ha 8) _
  · exact S.pow_mem (ha 9) _
  · exact S.zero_mem

/-! ### The own observations of one lane word -/

section Obs

variable {Bat : Type} [BatchedLayer K Bat]

theorem obs_apply_eq (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) :
    obs (Bat := Bat) π B ch c w =
      ownRead (Bat := Bat) (F := F) c (R0Z.PayloadSplit.L (Bat := Bat) π B ch (Pi.single c w)) := rfl

theorem ownRead_claim (c : Fin 29) (v : Payload K Bat) (j : Fin 3) :
    ownRead (Bat := Bat) (F := F) c v (.claim j) = v (.pointClaim j c) := rfl
theorem ownRead_extra (c : Fin 29) (v : Payload K Bat) :
    ownRead (Bat := Bat) (F := F) c v .extra = v (.extraClaim c) := rfl
theorem ownRead_ood (c : Fin 29) (v : Payload K Bat) (j : Fin 2) :
    ownRead (Bat := Bat) (F := F) c v (.ood j) = v (.ood j c) := rfl
theorem ownRead_opened (c : Fin 29) (v : Payload K Bat) (q : Fin 262144) (s : Fin 4) :
    ownRead (Bat := Bat) (F := F) c v (.opened q s) = v (.opened q s c) := rfl

theorem obs_claim (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) (j : Fin 3) :
    obs (Bat := Bat) π B ch c w (.claim j) = ∑ s, eqWeight (openingPoints (alpha ch) j) s * w s := by
  rw [obs_apply_eq, ownRead_claim, L_pointClaim_lp, lp_pointClaim, claimsLinear_sum,
    Pi.single_eq_same]

theorem obs_extra (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) :
    obs (Bat := Bat) π B ch c w .extra = ∑ i, libraWeight (alpha ch) i * w (π.symm i) := by
  rw [obs_apply_eq, ownRead_extra, L_extraClaim_lp, lp_extraClaim, extraLinear_sum,
    Pi.single_eq_same]

theorem obs_ood (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) (j : Fin 2) :
    obs (Bat := Bat) π B ch c w (.ood j) = oodLinear (ch.circle j) (fun i => w (π.symm i)) := by
  rw [obs_apply_eq, ownRead_ood, L_ood_lp, lp_ood, Pi.single_eq_same]

theorem obs_opened (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) (q : Fin 262144) (s : Fin 4) :
    obs (Bat := Bat) π B ch c w (.opened q s) =
      if q ∈ ch.queries then
        exactInitialLinear (fun i => w (π.symm i)) (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)
      else 0 := by
  rw [obs_apply_eq, ownRead_opened, L_opened_lp, lp_opened, Pi.single_eq_same]

theorem ood_sum (z : Point K) (m : InitialMessage K) :
    oodLinear z m = ∑ i, m i * rustEvalRow i z.1.1 z.1.2 := by
  rw [functional_eq_sum]
  simp only [oodLinear_unit]

theorem opened_sum (m : InitialMessage K) (idx : Fin 1048576) :
    exactInitialLinear m idx = ∑ i, m i * rustEvalRow i (storedX idx) (storedY idx) := by
  have h := functional_eq_sum ((LinearMap.proj idx).comp (exactInitialLinear (E := K))) m
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h
  rw [h]
  simp only [encoder_unit]

/-- Membership of the own observations of a lane word with values in `S`,
`F ≤ S ≤ K₄`. -/
theorem obs_mem (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (c : Fin 29) (S : Subfield K) (hSK : ∀ x, x ∈ S → x ∈ K4 B hB)
    (hFS : ∀ x, x ∈ F → x ∈ S) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    (w : Fin 1024 → K) (hw : ∀ s, w s ∈ S) :
    (∀ j, obs (Bat := Bat) π B ch c w (.claim j) ∈ K4 B hB) ∧
      obs (Bat := Bat) π B ch c w .extra ∈ K4 B hB ∧
      (∀ j, obs (Bat := Bat) π B ch c w (.ood j) ∈ K4 B hB) ∧
      (∀ q s, obs (Bat := Bat) π B ch c w (.opened q s) ∈ S) := by
  refine ⟨fun j => ?_, ?_, fun j => ?_, fun q s => ?_⟩
  · rw [obs_claim]
    exact sum_mem (fun s _ => (K4 B hB).mul_mem
      (eqWeight_mem _ (fun b => openingPoints_mem _ ha j b) s) (hSK _ (hw s)))
  · rw [obs_extra]
    exact sum_mem (fun i _ => (K4 B hB).mul_mem (libraWeight_mem _ ha i) (hSK _ (hw _)))
  · rw [obs_ood, ood_sum]
    exact sum_mem (fun i _ => (K4 B hB).mul_mem (hSK _ (hw _))
      (rustEvalRow_mem _ i (hz j).1 (hz j).2))
  · rw [obs_opened]
    split_ifs
    · rw [opened_sum]
      exact sum_mem (fun i _ => S.mul_mem (hw _)
        (rustEvalRow_mem S i (hFS _ (algebraMap_mem F _)) (hFS _ (algebraMap_mem F _))))
    · exact S.zero_mem

theorem obs_opened_zero (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29)
    (w : Fin 1024 → K) (q : Fin 262144) (s : Fin 4) (hq : q ∉ ch.queries) :
    obs (Bat := Bat) π B ch c w (.opened q s) = 0 := by
  rw [obs_opened, if_neg hq]

end Obs

/-! ### Limb layouts -/

/-- The base limb of an `F` value. -/
def limbF (x : K) : F := if h : x ∈ F then ⟨x, h⟩ else 0

theorem limbF_coe {x : K} (hx : x ∈ F) : (limbF (F := F) x : K) = x := by
  unfold limbF
  rw [dif_pos hx]

section Layout

variable {n : ℕ}

def iClaim (j : Fin 3) (k : Fin 4) : Fin (24 + n) := ⟨4 * j.val + k.val, by omega⟩
def iExtra (k : Fin 4) : Fin (24 + n) := ⟨12 + k.val, by omega⟩
def iOod (j : Fin 2) (k : Fin 4) : Fin (24 + n) := ⟨16 + 4 * j.val + k.val, by omega⟩

end Layout

/-- The C1 opened coordinate of list position `i`, slot `s`. -/
def iOpenB {n : ℕ} (i : Fin n) (s : Fin 4) : Fin (24 + 4 * n) := ⟨24 + 4 * i.val + s.val, by omega⟩

/-- The H1 opened coordinate of list position `i`, slot `s`, limb `k`. -/
def iOpenE {n : ℕ} (i : Fin n) (s : Fin 4) (k : Fin 4) : Fin (24 + 16 * n) :=
  ⟨24 + 16 * i.val + 4 * s.val + k.val, by omega⟩

variable (B : PackBasis F) (hB : PackField B)

/-- C1 own-cell assembly from `24 + 4n` base limbs. -/
def iotaC1 (l : List (Fin 262144)) :
    (Fin (24 + 4 * l.length) → F) →ₗ[F] (R1Z.PredicateR1.OwnCell → K) where
  toFun v := fun cell => match cell with
    | .claim j => pack4 B (fun k => (v (iClaim j k) : K))
    | .extra => pack4 B (fun k => (v (iExtra k) : K))
    | .ood j => pack4 B (fun k => (v (iOod j k) : K))
    | .opened q s => if h : ∃ i : Fin l.length, l.get i = q then
        (v (iOpenB (Classical.choose h) s) : K) else 0
  map_add' v w := by
    funext cell
    cases cell with
    | claim j => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | extra => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | ood j => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | opened q s =>
      simp only [Pi.add_apply]
      split_ifs <;> simp
  map_smul' c v := by
    funext cell
    cases cell with
    | claim j => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | extra => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | ood j => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | opened q s =>
      simp only [Pi.smul_apply, RingHom.id_apply, fsmul_eq]
      split_ifs <;> simp

/-- H1 own-cell assembly from `24 + 16n` limbs (opened cells four limbs). -/
def iotaH1 (l : List (Fin 262144)) :
    (Fin (24 + 16 * l.length) → F) →ₗ[F] (R1Z.PredicateR1.OwnCell → K) where
  toFun v := fun cell => match cell with
    | .claim j => pack4 B (fun k => (v (iClaim j k) : K))
    | .extra => pack4 B (fun k => (v (iExtra k) : K))
    | .ood j => pack4 B (fun k => (v (iOod j k) : K))
    | .opened q s => if h : ∃ i : Fin l.length, l.get i = q then
        pack4 B (fun k => (v (iOpenE (Classical.choose h) s k) : K)) else 0
  map_add' v w := by
    funext cell
    cases cell with
    | claim j => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | extra => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | ood j => simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
    | opened q s =>
      simp only [Pi.add_apply]
      split_ifs
      · simp only [Pi.add_apply, Subfield.coe_add, pack4]; ring
      · simp
  map_smul' c v := by
    funext cell
    cases cell with
    | claim j => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | extra => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | ood j => simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        fsmul_eq, pack4]; ring
    | opened q s =>
      simp only [Pi.smul_apply, RingHom.id_apply, fsmul_eq]
      split_ifs
      · simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, pack4]; ring
      · simp

/-- Common part of the two flattenings (claims, extra, OOD). -/
def flatHead (u : R1Z.PredicateR1.OwnCell → K) (i : ℕ) (h : i < 24) : F :=
  if h1 : i < 12 then limbs B hB (u (.claim ⟨i / 4, by omega⟩)) ⟨i % 4, by omega⟩
  else if h2 : i < 16 then limbs B hB (u .extra) ⟨i - 12, by omega⟩
  else limbs B hB (u (.ood ⟨(i - 16) / 4, by omega⟩)) ⟨(i - 16) % 4, by omega⟩

/-- C1 flattening (the inverse of `iotaC1` on its image). -/
def flatC1 (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) :
    Fin (24 + 4 * l.length) → F := fun i =>
  if h : i.val < 24 then flatHead B hB u i.val h
  else limbF (u (.opened (l.get ⟨(i.val - 24) / 4, by omega⟩) ⟨(i.val - 24) % 4, by omega⟩))

/-- H1 flattening. -/
def flatH1 (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) :
    Fin (24 + 16 * l.length) → F := fun i =>
  if h : i.val < 24 then flatHead B hB u i.val h
  else limbs B hB (u (.opened (l.get ⟨(i.val - 24) / 16, by omega⟩) ⟨(i.val - 24) % 16 / 4, by omega⟩))
    ⟨(i.val - 24) % 4, by omega⟩

theorem flatHead_claim (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 3) (k : Fin 4) (h : 4 * j.val + k.val < 24) :
    flatHead B hB u (4 * j.val + k.val) h = limbs B hB (u (.claim j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  have e1 : (4 * j.val + k.val) / 4 = j.val := by omega
  have e2 : (4 * j.val + k.val) % 4 = k.val := by omega
  unfold flatHead
  rw [dif_pos (by omega)]
  congr <;> first | exact Fin.ext e1 | exact Fin.ext e2

theorem flatHead_extra (u : R1Z.PredicateR1.OwnCell → K) (k : Fin 4) (h : 12 + k.val < 24) :
    flatHead B hB u (12 + k.val) h = limbs B hB (u .extra) k := by
  have hk := k.isLt
  have e2 : 12 + k.val - 12 = k.val := by omega
  unfold flatHead
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr <;> first | exact Fin.ext e2

theorem flatHead_ood (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 2) (k : Fin 4)
    (h : 16 + 4 * j.val + k.val < 24) :
    flatHead B hB u (16 + 4 * j.val + k.val) h = limbs B hB (u (.ood j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  have e1 : (16 + 4 * j.val + k.val - 16) / 4 = j.val := by omega
  have e2 : (16 + 4 * j.val + k.val - 16) % 4 = k.val := by omega
  unfold flatHead
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr <;> first | exact Fin.ext e1 | exact Fin.ext e2

theorem flatC1_claim (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 3) (k : Fin 4) :
    flatC1 B hB l u (iClaim j k) = limbs B hB (u (.claim j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  unfold flatC1
  rw [dif_pos (show (iClaim (n := 4 * l.length) j k).val < 24 by simp only [iClaim]; omega)]
  exact flatHead_claim B hB u j k _

theorem flatC1_extra (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (k : Fin 4) :
    flatC1 B hB l u (iExtra k) = limbs B hB (u .extra) k := by
  have hk := k.isLt
  unfold flatC1
  rw [dif_pos (show (iExtra (n := 4 * l.length) k).val < 24 by simp only [iExtra]; omega)]
  exact flatHead_extra B hB u k _

theorem flatC1_ood (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 2) (k : Fin 4) :
    flatC1 B hB l u (iOod j k) = limbs B hB (u (.ood j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  unfold flatC1
  rw [dif_pos (show (iOod (n := 4 * l.length) j k).val < 24 by simp only [iOod]; omega)]
  exact flatHead_ood B hB u j k _

theorem flatC1_open (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K)
    (i : Fin l.length) (s : Fin 4) :
    flatC1 B hB l u (iOpenB i s) = limbF (u (.opened (l.get i) s)) := by
  have hi := i.isLt
  have hs := s.isLt
  have e1 : (24 + 4 * i.val + s.val - 24) / 4 = i.val := by omega
  have e2 : (24 + 4 * i.val + s.val - 24) % 4 = s.val := by omega
  unfold flatC1
  rw [dif_neg (show ¬ (iOpenB i s).val < 24 by simp only [iOpenB]; omega)]
  congr <;> first | exact Fin.ext e1 | exact Fin.ext e2

theorem flatH1_claim (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 3) (k : Fin 4) :
    flatH1 B hB l u (iClaim j k) = limbs B hB (u (.claim j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  unfold flatH1
  rw [dif_pos (show (iClaim (n := 16 * l.length) j k).val < 24 by simp only [iClaim]; omega)]
  exact flatHead_claim B hB u j k _

theorem flatH1_extra (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (k : Fin 4) :
    flatH1 B hB l u (iExtra k) = limbs B hB (u .extra) k := by
  have hk := k.isLt
  unfold flatH1
  rw [dif_pos (show (iExtra (n := 16 * l.length) k).val < 24 by simp only [iExtra]; omega)]
  exact flatHead_extra B hB u k _

theorem flatH1_ood (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K) (j : Fin 2) (k : Fin 4) :
    flatH1 B hB l u (iOod j k) = limbs B hB (u (.ood j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  unfold flatH1
  rw [dif_pos (show (iOod (n := 16 * l.length) j k).val < 24 by simp only [iOod]; omega)]
  exact flatHead_ood B hB u j k _

theorem flatH1_open (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K)
    (i : Fin l.length) (s : Fin 4) (k : Fin 4) :
    flatH1 B hB l u (iOpenE i s k) = limbs B hB (u (.opened (l.get i) s)) k := by
  have hi := i.isLt
  have hs := s.isLt
  have hk := k.isLt
  have e1 : (24 + 16 * i.val + 4 * s.val + k.val - 24) / 16 = i.val := by omega
  have e2 : (24 + 16 * i.val + 4 * s.val + k.val - 24) % 16 / 4 = s.val := by omega
  have e3 : (24 + 16 * i.val + 4 * s.val + k.val - 24) % 4 = k.val := by omega
  unfold flatH1
  rw [dif_neg (show ¬ (iOpenE i s k).val < 24 by simp only [iOpenE]; omega)]
  congr <;> first | exact Fin.ext e1 | exact Fin.ext e2 | exact Fin.ext e3

/-- `iotaC1 ∘ flatC1 = id` on own vectors of the C1 shape. -/
theorem iotaC1_flat (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K)
    (hc : ∀ j, u (.claim j) ∈ K4 B hB) (he : u .extra ∈ K4 B hB)
    (ho : ∀ j, u (.ood j) ∈ K4 B hB) (hp : ∀ (i : Fin l.length) s, u (.opened (l.get i) s) ∈ F)
    (hz : ∀ q s, q ∉ l → u (.opened q s) = 0) :
    iotaC1 B l (flatC1 B hB l u) = u := by
  funext cell
  cases cell with
  | claim j =>
    show pack4 B (fun k => (flatC1 B hB l u (iClaim j k) : K)) = _
    simp only [flatC1_claim]
    exact pack4_limbs B hB (hc j)
  | extra =>
    show pack4 B (fun k => (flatC1 B hB l u (iExtra k) : K)) = _
    simp only [flatC1_extra]
    exact pack4_limbs B hB he
  | ood j =>
    show pack4 B (fun k => (flatC1 B hB l u (iOod j k) : K)) = _
    simp only [flatC1_ood]
    exact pack4_limbs B hB (ho j)
  | opened q s =>
    show (if h : ∃ i : Fin l.length, l.get i = q then
        ((flatC1 B hB l u (iOpenB (Classical.choose h) s)) : K) else 0) = _
    split_ifs with h
    · rw [flatC1_open, limbF_coe (hp _ s), Classical.choose_spec h]
    · exact (hz q s (fun hm => h (List.mem_iff_get.1 hm))).symm

/-- `iotaH1 ∘ flatH1 = id` on own vectors of the H1 shape. -/
theorem iotaH1_flat (l : List (Fin 262144)) (u : R1Z.PredicateR1.OwnCell → K)
    (hc : ∀ j, u (.claim j) ∈ K4 B hB) (he : u .extra ∈ K4 B hB)
    (ho : ∀ j, u (.ood j) ∈ K4 B hB) (hp : ∀ (i : Fin l.length) s, u (.opened (l.get i) s) ∈ K4 B hB)
    (hz : ∀ q s, q ∉ l → u (.opened q s) = 0) :
    iotaH1 B l (flatH1 B hB l u) = u := by
  funext cell
  cases cell with
  | claim j =>
    show pack4 B (fun k => (flatH1 B hB l u (iClaim j k) : K)) = _
    simp only [flatH1_claim]
    exact pack4_limbs B hB (hc j)
  | extra =>
    show pack4 B (fun k => (flatH1 B hB l u (iExtra k) : K)) = _
    simp only [flatH1_extra]
    exact pack4_limbs B hB he
  | ood j =>
    show pack4 B (fun k => (flatH1 B hB l u (iOod j k) : K)) = _
    simp only [flatH1_ood]
    exact pack4_limbs B hB (ho j)
  | opened q s =>
    show (if h : ∃ i : Fin l.length, l.get i = q then
        pack4 B (fun k => ((flatH1 B hB l u (iOpenE (Classical.choose h) s k)) : K)) else 0) = _
    split_ifs with h
    · simp only [flatH1_open]
      rw [pack4_limbs B hB (hp _ s), Classical.choose_spec h]
    · exact (hz q s (fun hm => h (List.mem_iff_get.1 hm))).symm

/-! ### RF-obs and RF-col -/

section Lift

variable {Bat : Type} [BatchedLayer K Bat]

theorem base_of_Wsem {w : Fin 1024 → K} (hw : w ∈ Wsem (K := K) (F := F)) (s : Fin 1024) : w s ∈ F := by
  have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hw).1 s
  rw [Submodule.mem_comap] at h
  obtain ⟨y, hy⟩ := h
  rw [LinearMap.proj_apply] at hy
  rw [← hy]
  exact y.2

theorem K4_of_Wh1 {w : Fin 1024 → K} (hw : w ∈ Wh1 B hB) (s : Fin 1024) : w s ∈ K4 B hB := by
  have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hw).1 s
  rw [Submodule.mem_comap] at h
  exact (mem_K4F B hB).1 h

/-- **RF-obs, C1.** -/
theorem rf_obs_C1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB) :
    (Wsem (K := K) (F := F)).map (obs (Bat := Bat) π B ch c) ≤ LinearMap.range (iotaC1 B l) := by
  rintro u ⟨w, hw, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch c F (fun x hx => F_le_K4 B hB hx)
    (fun x hx => hx) ha hz w (base_of_Wsem hw)
  refine ⟨flatC1 B hB l (obs (Bat := Bat) π B ch c w), iotaC1_flat B hB l _ h1 h2 h3
    (fun i s => h4 _ s) (fun q s hql => ?_)⟩
  exact obs_opened_zero π B ch c w q s (by rw [hq, List.mem_toFinset]; exact hql)

/-- **RF-obs, H1.** -/
theorem rf_obs_H1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB) :
    (Wh1 B hB).map (obs (Bat := Bat) π B ch 26) ≤ LinearMap.range (iotaH1 B l) := by
  rintro u ⟨w, hw, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch 26 (K4 B hB) (fun x hx => hx)
    (fun x hx => F_le_K4 B hB hx) ha hz w (K4_of_Wh1 B hB hw)
  refine ⟨flatH1 B hB l (obs (Bat := Bat) π B ch 26 w), iotaH1_flat B hB l _ h1 h2 h3
    (fun i s => h4 _ s) (fun q s hql => ?_)⟩
  exact obs_opened_zero π B ch 26 w q s (by rw [hq, List.mem_toFinset]; exact hql)

/-- The checker's C1 column matrix for the selected rows. -/
def colC1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29) (l : List (Fin 262144))
    {w : ℕ} (sel : Fin w → Fin 1024) : Fin (24 + 4 * l.length) → Fin w → F :=
  fun i t => flatC1 B hB l (obs (Bat := Bat) π B ch c (c1Src (sel t))) i

/-- The checker's H1 column matrix for the selected (row, limb) pairs. -/
def colH1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : List (Fin 262144))
    {w : ℕ} (sel : Fin w → Fin 1024 × Fin 4) : Fin (24 + 16 * l.length) → Fin w → F :=
  fun i t => flatH1 B hB l (obs (Bat := Bat) π B ch 26 (h1Src B (sel t).1 (sel t).2)) i

theorem balWord_mem (S : Subfield K) (d r : Fin 1024) {x : K} (hx : x ∈ S) (s : Fin 1024) :
    balWord d r x s ∈ S := by
  unfold balWord
  split_ifs
  · exact hx
  · exact S.neg_mem hx
  · exact S.zero_mem

/-- **RF-col, C1.** -/
theorem rf_col_C1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    {w : ℕ} (sel : Fin w → Fin 1024) (t : Fin w) :
    obs (Bat := Bat) π B ch c (c1Src (sel t)) =
      iotaC1 B l (R1Z.CertSound.col (colC1 (Bat := Bat) B hB π ch c l sel) t) := by
  obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch c F (fun x hx => F_le_K4 B hB hx)
    (fun x hx => hx) ha hz (c1Src (sel t)) (balWord_mem F 1023 (sel t) F.one_mem)
  refine (iotaC1_flat B hB l _ h1 h2 h3 (fun i s => h4 _ s) (fun q s hql => ?_)).symm
  exact obs_opened_zero π B ch c _ q s (by rw [hq, List.mem_toFinset]; exact hql)

/-- **RF-col, H1.** -/
theorem rf_col_H1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    {w : ℕ} (sel : Fin w → Fin 1024 × Fin 4) (t : Fin w) :
    obs (Bat := Bat) π B ch 26 (h1Src B (sel t).1 (sel t).2) =
      iotaH1 B l (R1Z.CertSound.col (colH1 (Bat := Bat) B hB π ch l sel) t) := by
  obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch 26 (K4 B hB) (fun x hx => hx)
    (fun x hx => F_le_K4 B hB hx) ha hz (h1Src B (sel t).1 (sel t).2)
    (balWord_mem (K4 B hB) 0 (sel t).1 (towerBasis_mem_K4 B hB _))
  refine (iotaH1_flat B hB l _ h1 h2 h3 (fun i s => h4 _ s) (fun q s hql => ?_)).symm
  exact obs_opened_zero π B ch 26 _ q s (by rw [hq, List.mem_toFinset]; exact hql)

/-- Closed form of the lift columns: the Rust `raw_c` values (`eq`, `h_weight`,
`evalrow`) of row `r`, differenced against the dependent row `d` when `r` is
copy-inactive (z9c.rs:224-233). -/
theorem obs_balWord_claim (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) (j : Fin 3) :
    obs (Bat := Bat) π B ch c (balWord d r x) (.claim j) =
      x * rustEq (rustPoints (alpha ch) j) r -
        (if r ∈ copyInactiveRows then x * rustEq (rustPoints (alpha ch) j) d else 0) := by
  rw [obs_claim, sum_mul_balWord _ d r hr, openingPoints_eq, rustEq_eq, rustEq_eq]

theorem obs_balWord_extra (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) :
    obs (Bat := Bat) π B ch c (balWord d r x) .extra =
      x * rustHWeight (alpha ch) (π r) -
        (if r ∈ copyInactiveRows then x * rustHWeight (alpha ch) (π d) else 0) := by
  rw [obs_extra, ← Equiv.sum_comp π]
  simp only [Equiv.symm_apply_apply]
  rw [sum_mul_balWord (fun s => libraWeight (alpha ch) (π s)) d r hr x]
  rfl

theorem obs_balWord_ood (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) (j : Fin 2) :
    obs (Bat := Bat) π B ch c (balWord d r x) (.ood j) =
      x * rustEvalRow (π r) (ch.circle j).1.1 (ch.circle j).1.2 -
        (if r ∈ copyInactiveRows then
          x * rustEvalRow (π d) (ch.circle j).1.1 (ch.circle j).1.2 else 0) := by
  rw [obs_ood, functional_balWord _ π d r hr x, oodLinear_unit, oodLinear_unit]

theorem obs_balWord_opened (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) (q : Fin 262144) (s : Fin 4) (hq : q ∈ ch.queries) :
    obs (Bat := Bat) π B ch c (balWord d r x) (.opened q s) =
      x * rustEvalRow (π r) (storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex q s))
          (storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)) -
        (if r ∈ copyInactiveRows then
          x * rustEvalRow (π d) (storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex q s))
            (storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)) else 0) := by
  rw [obs_opened, if_pos hq]
  have hφ := functional_balWord
    ((LinearMap.proj (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)).comp
      (exactInitialLinear (E := K))) π d r hr x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hφ
  rw [hφ, encoder_unit, encoder_unit]

end Lift

#print axioms algebraMap_mem
#print axioms openingPoints_mem
#print axioms obs_claim
#print axioms obs_opened
#print axioms ood_sum
#print axioms opened_sum
#print axioms obs_mem
#print axioms flatC1_open
#print axioms flatH1_open
#print axioms iotaC1_flat
#print axioms iotaH1_flat
#print axioms rf_obs_C1
#print axioms rf_obs_H1
#print axioms rf_col_C1
#print axioms rf_col_H1
#print axioms obs_balWord_claim
#print axioms obs_balWord_extra
#print axioms obs_balWord_ood
#print axioms obs_balWord_opened

end R1Z.RfObs

end
