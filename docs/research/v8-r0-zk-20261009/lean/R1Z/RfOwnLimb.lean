import R1Z.RfObs

/-! D49.4 C2: RF-own with its limb assembly (zf1/DESIGN-P-CERT.txt §0 "own",
§2.3 RF-own), Lean side.

The checker stacks the own coordinates of the twelve mask lanes in the order
m0..m9 (lanes 16..25), G (27), D (28) (z4/z9.rs:957-1001 `LANES`, `phys`,
`own_width`): each mask-only block is the C1 layout of `RfObs.iotaC1`
(`24 + 4n` base limbs, 112 at n = 22), each K₄ block the H1 layout of
`RfObs.iotaH1` (`24 + 16n` limbs, 376 at n = 22); 1,872 in all at n = 22.

* `iotaO l` is that coordinate embedding `F^a → Payload`.
* `flatO l u` reads the coordinates of a payload `u` block by block.
* `rf_own`: for **every** mask tape `m`, `ownMap m = iotaO l (flatO l (ownMap m))`,
  given the decoder facts (query set `l.toFinset`, α and the circle points in
  `K₄`).  Hence the `rf_own` premise of `CertR1.qprime_of_cert` /
  `bcondG_of_cert` holds for any source family `src` with
  `Own i t = flatO l (ownMap (src t)) i` (`rf_own_col`).

The closed form of these columns for the checker's sources is
`RfOwn.ownMap_maskOnlySrc/gSrc/dSrc` (the Rust `raw_c` values); matching the
extracted Rust column builders to it is C3. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfOwnLimb

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.K4
open R1Z.PredicateR1 R1Z.RfSrc R1Z.RfOwn R1Z.RfChain R1Z.RfObs

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Layout -/

/-- Base block width `24 + 4n`. -/
abbrev wB (n : ℕ) : ℕ := 24 + 4 * n
/-- K₄ block width `24 + 16n`. -/
abbrev wE (n : ℕ) : ℕ := 24 + 16 * n
/-- Stacked width `10·wB + 2·wE`. -/
abbrev wO (n : ℕ) : ℕ := 10 * wB n + 2 * wE n

theorem posB_lt {n : ℕ} (i : Fin 10) (k : Fin (wB n)) : i.val * wB n + k.val < wO n := by
  have h1 : i.val * wB n ≤ 9 * wB n := Nat.mul_le_mul_right _ (by omega)
  have hk := k.isLt
  unfold wO
  omega

theorem posE_lt {n : ℕ} (e : Fin 2) (k : Fin (wE n)) : 10 * wB n + e.val * wE n + k.val < wO n := by
  have h1 : e.val * wE n ≤ 1 * wE n := Nat.mul_le_mul_right _ (by omega)
  have hk := k.isLt
  unfold wO
  omega

/-- Coordinate `k` of mask-only block `i`. -/
def posB {n : ℕ} (i : Fin 10) (k : Fin (wB n)) : Fin (wO n) := ⟨i.val * wB n + k.val, posB_lt i k⟩
/-- Coordinate `k` of K₄ block `e` (0 = G, 1 = D). -/
def posE {n : ℕ} (e : Fin 2) (k : Fin (wE n)) : Fin (wO n) :=
  ⟨10 * wB n + e.val * wE n + k.val, posE_lt e k⟩

/-- The own cells of lane `c` of a payload. -/
def laneObs {Bat : Type} (u : Payload K Bat) (c : Fin 29) : OwnCell → K := fun oc =>
  match oc with
  | .claim j => u (.pointClaim j c)
  | .extra => u (.extraClaim c)
  | .ood j => u (.ood j c)
  | .opened q s => u (.opened q s c)

variable (B : PackBasis F) (hB : PackField B)

/-- The lane-`c` part of the coordinate embedding. -/
def laneOwnL (l : List (Fin 262144)) (c : Fin 29) :
    (Fin (wO l.length) → F) →ₗ[F] (OwnCell → K) :=
  if h : 16 ≤ c.val ∧ c.val < 26 then
    (iotaC1 B l).comp (LinearMap.funLeft F F (posB ⟨c.val - 16, by omega⟩))
  else if h' : 27 ≤ c.val then
    (iotaH1 B l).comp (LinearMap.funLeft F F (posE ⟨c.val - 27, by omega⟩))
  else 0

/-- The checker's own coordinate embedding `ιo`. -/
def iotaO {Bat : Type} (l : List (Fin 262144)) : (Fin (wO l.length) → F) →ₗ[F] Payload K Bat :=
  LinearMap.pi fun cell => match cell with
  | .pointClaim j c => (LinearMap.proj (OwnCell.claim j)).comp (laneOwnL B l c)
  | .extraClaim c => (LinearMap.proj OwnCell.extra).comp (laneOwnL B l c)
  | .ood j c => (LinearMap.proj (OwnCell.ood j)).comp (laneOwnL B l c)
  | .opened q s c => (LinearMap.proj (OwnCell.opened q s)).comp (laneOwnL B l c)
  | _ => 0

/-- The checker's own coordinates of a payload, block by block. -/
def flatO {Bat : Type} (l : List (Fin 262144)) (u : Payload K Bat) : Fin (wO l.length) → F :=
  fun p =>
    if h : p.val < 10 * wB l.length then
      flatC1 B hB l (laneObs u ⟨16 + p.val / wB l.length, by
        have : p.val / wB l.length < 10 :=
          (Nat.div_lt_iff_lt_mul (by unfold wB; omega)).2 h
        omega⟩) ⟨p.val % wB l.length, Nat.mod_lt _ (by unfold wB; omega)⟩
    else
      flatH1 B hB l (laneObs u ⟨27 + (p.val - 10 * wB l.length) / wE l.length, by
        have hp := p.isLt
        unfold wO at hp
        have : (p.val - 10 * wB l.length) / wE l.length < 2 :=
          (Nat.div_lt_iff_lt_mul (by unfold wE; omega)).2 (by omega)
        omega⟩) ⟨(p.val - 10 * wB l.length) % wE l.length, Nat.mod_lt _ (by unfold wE; omega)⟩

theorem flatO_posB {Bat : Type} (l : List (Fin 262144)) (u : Payload K Bat) (i : Fin 10)
    (k : Fin (wB l.length)) :
    flatO B hB l u (posB i k) = flatC1 B hB l (laneObs u ⟨16 + i.val, by omega⟩) k := by
  have hk := k.isLt
  have hpos : 0 < wB l.length := by unfold wB; omega
  have e1 : (i.val * wB l.length + k.val) / wB l.length = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hk, Nat.zero_add]
  have e2 : (i.val * wB l.length + k.val) % wB l.length = k.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have hlt : (posB (n := l.length) i k).val < 10 * wB l.length := by
    have h1 : i.val * wB l.length ≤ 9 * wB l.length := Nat.mul_le_mul_right _ (by omega)
    show i.val * wB l.length + k.val < _
    omega
  unfold flatO
  rw [dif_pos hlt]
  congr <;> first
    | (apply Fin.ext; show 16 + (i.val * wB l.length + k.val) / wB l.length = 16 + i.val; rw [e1])
    | (apply Fin.ext; show (i.val * wB l.length + k.val) % wB l.length = k.val; rw [e2])
    | (show 16 + (i.val * wB l.length + k.val) / wB l.length = 16 + i.val; rw [e1])
    | (show (i.val * wB l.length + k.val) % wB l.length = k.val; rw [e2])
    | (show (i.val * wB l.length + k.val) / wB l.length = i.val; rw [e1])

theorem flatO_posE {Bat : Type} (l : List (Fin 262144)) (u : Payload K Bat) (e : Fin 2)
    (k : Fin (wE l.length)) :
    flatO B hB l u (posE e k) = flatH1 B hB l (laneObs u ⟨27 + e.val, by omega⟩) k := by
  have hk := k.isLt
  have hpos : 0 < wE l.length := by unfold wE; omega
  have e0 : 10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length =
      e.val * wE l.length + k.val := by omega
  have e1 : (e.val * wE l.length + k.val) / wE l.length = e.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hk, Nat.zero_add]
  have e2 : (e.val * wE l.length + k.val) % wE l.length = k.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have hlt : ¬ (posE (n := l.length) e k).val < 10 * wB l.length := by
    show ¬ 10 * wB l.length + e.val * wE l.length + k.val < _
    omega
  unfold flatO
  rw [dif_neg hlt]
  congr <;> first
    | (apply Fin.ext; show 27 + (10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length) /
        wE l.length = 27 + e.val; rw [e0, e1])
    | (apply Fin.ext; show (10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length) %
        wE l.length = k.val; rw [e0, e2])
    | (show 27 + (10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length) /
        wE l.length = 27 + e.val; rw [e0, e1])
    | (show (10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length) /
        wE l.length = e.val; rw [e0, e1])
    | (show (10 * wB l.length + e.val * wE l.length + k.val - 10 * wB l.length) %
        wE l.length = k.val; rw [e0, e2])

/-! ### `ιo ∘ flatO = id` on own payloads -/

/-- The hypotheses of `iotaC1_flat` for one lane. -/
def BaseLane (l : List (Fin 262144)) (v : OwnCell → K) : Prop :=
  (∀ j, v (.claim j) ∈ K4 B hB) ∧ v .extra ∈ K4 B hB ∧ (∀ j, v (.ood j) ∈ K4 B hB) ∧
    (∀ (i : Fin l.length) s, v (.opened (l.get i) s) ∈ F) ∧ (∀ q s, q ∉ l → v (.opened q s) = 0)

/-- The hypotheses of `iotaH1_flat` for one lane. -/
def ExtLane (l : List (Fin 262144)) (v : OwnCell → K) : Prop :=
  (∀ j, v (.claim j) ∈ K4 B hB) ∧ v .extra ∈ K4 B hB ∧ (∀ j, v (.ood j) ∈ K4 B hB) ∧
    (∀ (i : Fin l.length) s, v (.opened (l.get i) s) ∈ K4 B hB) ∧
      (∀ q s, q ∉ l → v (.opened q s) = 0)

theorem laneOwnL_flatO {Bat : Type} (l : List (Fin 262144)) (u : Payload K Bat)
    (hBl : ∀ i : Fin 10, BaseLane B hB l (laneObs u ⟨16 + i.val, by omega⟩))
    (hEl : ∀ e : Fin 2, ExtLane B hB l (laneObs u ⟨27 + e.val, by omega⟩))
    (h0 : ∀ c : Fin 29, (c.val < 16 ∨ c.val = 26) → laneObs u c = 0) (c : Fin 29) :
    laneOwnL B l c (flatO B hB l u) = laneObs u c := by
  unfold laneOwnL
  by_cases h : 16 ≤ c.val ∧ c.val < 26
  · rw [dif_pos h, LinearMap.comp_apply]
    have hf : LinearMap.funLeft F F (posB (n := l.length) ⟨c.val - 16, by omega⟩) (flatO B hB l u) =
        flatC1 B hB l (laneObs u ⟨16 + (c.val - 16), by omega⟩) := by
      funext k
      exact flatO_posB B hB l u _ k
    rw [hf]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hBl ⟨c.val - 16, by omega⟩
    rw [iotaC1_flat B hB l _ h1 h2 h3 h4 h5]
    congr 1
    exact Fin.ext (by simp only; omega)
  · rw [dif_neg h]
    by_cases h' : 27 ≤ c.val
    · rw [dif_pos h', LinearMap.comp_apply]
      have hf : LinearMap.funLeft F F (posE (n := l.length) ⟨c.val - 27, by omega⟩) (flatO B hB l u) =
          flatH1 B hB l (laneObs u ⟨27 + (c.val - 27), by omega⟩) := by
        funext k
        exact flatO_posE B hB l u _ k
      rw [hf]
      obtain ⟨h1, h2, h3, h4, h5⟩ := hEl ⟨c.val - 27, by omega⟩
      rw [iotaH1_flat B hB l _ h1 h2 h3 h4 h5]
      congr 1
      exact Fin.ext (by simp only; omega)
    · rw [dif_neg h', LinearMap.zero_apply]
      exact (h0 c (by omega)).symm

theorem iotaO_flatO {Bat : Type} (l : List (Fin 262144)) (u : Payload K Bat)
    (hBl : ∀ i : Fin 10, BaseLane B hB l (laneObs u ⟨16 + i.val, by omega⟩))
    (hEl : ∀ e : Fin 2, ExtLane B hB l (laneObs u ⟨27 + e.val, by omega⟩))
    (h0 : ∀ c : Fin 29, (c.val < 16 ∨ c.val = 26) → laneObs u c = 0)
    (hm : u .maskSum = 0) (hs : ∀ j i, u (.semanticCoeff j i) = 0) (hi : u .inactiveSum = 0)
    (hb : ∀ b, u (.bat b) = 0) :
    iotaO (Bat := Bat) B l (flatO B hB l u) = u := by
  have hL := laneOwnL_flatO B hB l u hBl hEl h0
  funext cell
  cases cell with
  | maskSum => exact hm.symm
  | semanticCoeff j i => exact (hs j i).symm
  | inactiveSum => exact hi.symm
  | bat b => exact (hb b).symm
  | pointClaim j c => exact congrFun (hL c) (.claim j)
  | extraClaim c => exact congrFun (hL c) .extra
  | ood j c => exact congrFun (hL c) (.ood j)
  | opened q s c => exact congrFun (hL c) (.opened q s)

/-! ### `ownMap` of a mask tape -/

section Own

variable {Bat : Type} [BatchedLayer K Bat]

theorem ownMap_lane (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (m : M K F) (c : Fin 29) :
    laneObs (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m) c =
      obs (Bat := Bat) π B ch c (pureTrace B m c) := by
  have hA : (A (Bat := Bat) π B ch).comp inlM m =
      R0Z.PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) := R0Z.PureRounds.A_pure π B ch m
  have hown : ∀ cell, R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m cell =
      R0Z.SilentReduction.ownProj (F := F) ((A (Bat := Bat) π B ch).comp inlM m) cell :=
    fun _ => rfl
  funext oc
  cases oc with
  | claim j =>
    show R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m (.pointClaim j c) = _
    rw [hown, hA, ownProj_pointClaim, L_pointClaim_lp, lp_pointClaim, claimsLinear_sum, obs_claim]
  | extra =>
    show R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m (.extraClaim c) = _
    rw [hown, hA, ownProj_extraClaim, L_extraClaim_lp, lp_extraClaim, extraLinear_sum, obs_extra]
  | ood j =>
    show R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m (.ood j c) = _
    rw [hown, hA, ownProj_ood, L_ood_lp, lp_ood, obs_ood]
  | opened q s =>
    show R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m (.opened q s c) = _
    rw [hown, hA, ownProj_opened, L_opened_lp, lp_opened, obs_opened]

theorem balance_mem (S : Subfield K) (d : Fin 1024) {w : Fin 1024 → K} (hw : ∀ s, w s ∈ S)
    (r : Fin 1024) : balance d w r ∈ S := by
  unfold balance
  split_ifs
  · exact S.neg_mem (sum_mem (fun s _ => hw s))
  · exact hw r

theorem pureTrace_maskOnly_mem (m : M K F) (i : Fin 10) (s : Fin 1024) :
    pureTrace B m ⟨16 + i.val, by omega⟩ s ∈ F := by
  rw [R0Z.PureRounds.pureTrace_maskOnly_word]
  exact balance_mem F 0 (fun _ => SetLike.coe_mem _) s

theorem pureTrace_ext_mem (m : M K F) (e : Fin 2) (s : Fin 1024) :
    pureTrace B m ⟨27 + e.val, by omega⟩ s ∈ K4 B hB := by
  have hp : ∀ (lane : Fin 3) (r : Fin 1024),
      extensionRaw B (Sum.elim 0 (pureAff m)) lane r ∈ K4 B hB := fun lane r =>
    (mem_K4_iff_pack4 B hB).2 ⟨_, fun _ => SetLike.coe_mem _, rfl⟩
  fin_cases e
  · show pureTrace B m 27 s ∈ K4 B hB
    rw [R0Z.PureRounds.pureTrace_G_word]
    exact balance_mem _ 0 (hp 0) s
  · show pureTrace B m 28 s ∈ K4 B hB
    rw [R0Z.PureRounds.pureTrace_D_word]
    exact balance_mem _ 0 (hp 2) s

/-- **RF-own.**  Every mask tape's own payload is the `ιo`-image of its
checker coordinates. -/
theorem rf_own (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : List (Fin 262144))
    (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB) (m : M K F) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m =
      iotaO (Bat := Bat) B l (flatO B hB l (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m)) := by
  have hnq : ∀ q, q ∉ l → q ∉ ch.queries := fun q hql => by rw [hq, List.mem_toFinset]; exact hql
  refine (iotaO_flatO B hB l _ (fun i => ?_) (fun e => ?_) (fun c hc => ?_) rfl
    (fun _ _ => rfl) rfl (fun _ => rfl)).symm
  · rw [ownMap_lane]
    obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch _ F (fun x hx => F_le_K4 B hB hx)
      (fun x hx => hx) ha hz _ (pureTrace_maskOnly_mem B m i)
    exact ⟨h1, h2, h3, fun i s => h4 _ s,
      fun q s hql => obs_opened_zero π B ch _ _ q s (hnq q hql)⟩
  · rw [ownMap_lane]
    obtain ⟨h1, h2, h3, h4⟩ := obs_mem (Bat := Bat) π B hB ch _ (K4 B hB) (fun x hx => hx)
      (fun x hx => F_le_K4 B hB hx) ha hz _ (pureTrace_ext_mem B hB m e)
    exact ⟨h1, h2, h3, fun i s => h4 _ s,
      fun q s hql => obs_opened_zero π B ch _ _ q s (hnq q hql)⟩
  · rw [ownMap_lane, pureTrace_fixed B m c hc]
    exact map_zero _

/-- **RF-own for a source family**: the `rf_own` premise with
`ιo = iotaO l` and `Own i t = flatO l (ownMap (src t)) i`. -/
theorem rf_own_col (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : List (Fin 262144))
    (hq : ch.queries = l.toFinset) (ha : ∀ j, alpha ch j ∈ K4 B hB)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    {N : ℕ} (src : Fin N → M K F) (t : Fin N) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (src t) =
      iotaO (Bat := Bat) B l (R1Z.CertSound.col
        (fun i t' => flatO B hB l (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (src t')) i) t) :=
  rf_own B hB π ch l hq ha hz (src t)

end Own

#print axioms posB_lt
#print axioms flatO_posB
#print axioms flatO_posE
#print axioms laneOwnL_flatO
#print axioms iotaO_flatO
#print axioms ownMap_lane
#print axioms pureTrace_maskOnly_mem
#print axioms pureTrace_ext_mem
#print axioms rf_own
#print axioms rf_own_col

end R1Z.RfOwnLimb

end
