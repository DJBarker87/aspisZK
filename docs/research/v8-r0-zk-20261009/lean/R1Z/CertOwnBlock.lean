import R1Z.RfOwnLimb
import R1Z.CertData

/-! D62 builder 3: the own block layout, without Aeneas types.  For a referenced
source of kind `j` (mask lane `j < 10`, G = 10, D = 11), row `r ≥ 1` and limb
`k`, every `flatO` coordinate of `ownMap (mkSrc j r k)` is `φ` of the
lane-blocked matrix `blockM` (block starts `stOf`), given the per-lane entry
identifications `hC` (mask lane: `flatC1 (obs (balWord 0 r 1))`) and `hE`
(G/D: `flatH1 (obs (balWord 0 r (towerBasis k)))`), which the extracted builder
supplies (`CertOwnIdent`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertOwn
open R0P R1Z.RfChain R1Z.RfOwn R1Z.RfObs R1Z.RfSrc R1Z.PredicateR1 R1Z.RfOwnLimb
open R0Z.K4 R0Z.HonestView R0Z.MaskLayout R0Z.Partition
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F)
  (φ : R1Z.CertData.ZP →+* ↥F)

/-- The Lean source of a referenced Rust source. -/
def mkSrc (j : ℕ) (r : Fin 1024) (k : Fin 4) : M K F :=
  if h : j < 10 then maskOnlySrc ⟨j, h⟩ r else if j = 10 then gSrc r k else dSrc r k

/-- The block starts of the stacked own coordinates. -/
def stOf (n : ℕ) (j : ℕ) : ℕ := if j < 10 then j * wB n else 10 * wB n + (j - 10) * wE n

theorem limbs_zero (hB : PackField B) (k : Fin 4) : limbs B hB (0 : K) k = 0 := by
  have hx : (0 : K) ∈ K4 B hB := (K4 B hB).zero_mem
  have e := pack4_limbs B hB hx
  have hz := (pack4_eq_zero_iff B (fun j => (limbs B hB (0 : K) j : K)) (fun j => (limbs B hB 0 j).2)).1 e k
  exact Subtype.ext hz

theorem limbF_zero : limbF (F := F) (0 : K) = 0 := by
  unfold limbF; rw [dif_pos F.zero_mem]; rfl

theorem flatC1_zero (hB : PackField B) (l : List (Fin 262144)) (i : Fin (24 + 4 * l.length)) :
    flatC1 B hB l (0 : OwnCell → K) i = 0 := by
  unfold flatC1 flatHead
  split_ifs <;> simp [limbs_zero B hB, limbF_zero]

theorem flatH1_zero (hB : PackField B) (l : List (Fin 262144)) (i : Fin (24 + 16 * l.length)) :
    flatH1 B hB l (0 : OwnCell → K) i = 0 := by
  unfold flatH1 flatHead
  split_ifs <;> simp [limbs_zero B hB]

variable {Bat : Type} [BatchedLayer K Bat]

/-- **Own block identification** for one referenced source. -/
theorem own_src_ident (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) 
    (ownf : ℕ → R1Z.CertData.ZP) (os : ℕ) (lanef wlf st : ℕ → ℕ)
    (t j : ℕ) (hj : j < 12) (r : Fin 1024) (hr : r ≠ 0) (k : Fin 4)
    (hst : st (lanef t) = stOf l.length j) (hw : wlf (lanef t) = if j < 10 then wB l.length else wE l.length)
    (hC : j < 10 → ∀ (c : Fin 29) (i : Fin (24 + 4 * l.length)),
      flatC1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r 1)) i = φ (ownf (t * os + i.val)))
    (hE : 10 ≤ j → ∀ (c : Fin 29) (i : Fin (24 + 16 * l.length)),
      flatH1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r (Mask.towerBasis B k))) i = φ (ownf (t * os + i.val)))
    (p : Fin (wO l.length)) :
    flatO B hB l (R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (mkSrc j r k)) p =
      φ (R1Z.CertData.blockM ownf os lanef wlf st p t) := by
  have hwB : wB l.length ≤ wE l.length := by unfold wB wE; omega
  unfold R1Z.CertData.blockM
  rw [hst, hw]
  unfold flatO
  by_cases hp : p.val < 10 * wB l.length
  · rw [dif_pos hp, ownMap_lane B π ch]
    have hpos : 0 < wB l.length := by unfold wB; omega
    have hb : p.val / wB l.length < 10 := (Nat.div_lt_iff_lt_mul hpos).2 hp
    by_cases hjb : j < 10 ∧ p.val / wB l.length = j
    · obtain ⟨hj10, hbj⟩ := hjb
      have e16 : (⟨16 + p.val / wB l.length, by omega⟩ : Fin 29) = ⟨16 + (⟨j, hj10⟩ : Fin 10).val, by omega⟩ :=
        Fin.ext (by simp [hbj])
      rw [e16]
      unfold mkSrc
      rw [dif_pos hj10, pureTrace_maskOnlySrc B ⟨j, hj10⟩ r hr]
      have hloc : p.val % wB l.length < wB l.length := Nat.mod_lt _ hpos
      have hlo : p.val - j * wB l.length = p.val % wB l.length := by
        have := Nat.div_add_mod p.val (wB l.length); rw [hbj, mul_comm] at this
        generalize j * wB l.length = A at this ⊢
        omega
      have hst' : stOf l.length j = j * wB l.length := by unfold stOf; rw [if_pos hj10]
      have hin : stOf l.length j ≤ p.val ∧ p.val < stOf l.length j + wB l.length := by
        rw [hst']
        have := Nat.div_add_mod p.val (wB l.length)
        rw [hbj, mul_comm] at this
        generalize j * wB l.length = A at this ⊢
        generalize p.val % wB l.length = R at this hloc
        constructor <;> omega
      simp only [if_pos hj10]
      rw [if_pos hin, hst', hlo]
      exact hC hj10 _ ⟨p.val % wB l.length, hloc⟩
    · have hz : pureTrace B ((mkSrc j r k : M K F)) ⟨16 + p.val / wB l.length, by omega⟩ = 0 := by
        unfold mkSrc
        by_cases hj10 : j < 10
        · rw [dif_pos hj10]
          exact pureTrace_maskOnlySrc_other B ⟨j, hj10⟩ r _ (fun h => hjb ⟨hj10, by
            have := congrArg Fin.val h; simp at this; omega⟩)
        · rw [dif_neg hj10]
          by_cases h10 : j = 10
          · rw [if_pos h10]; exact pureTrace_gSrc_other B r k _ (fun h => by
              have := congrArg Fin.val h; simp at this; omega)
          · rw [if_neg h10]; exact pureTrace_dSrc_other B r k _ (fun h => by
              have := congrArg Fin.val h; simp at this; omega)
      rw [hz, map_zero, flatC1_zero B hB, if_neg, map_zero]
      intro ⟨h1, h2⟩
      unfold stOf at h1 h2
      by_cases hj10 : j < 10
      · rw [if_pos hj10] at h1 h2
        rw [if_pos hj10] at h2
        apply hjb ⟨hj10, ?_⟩
        exact Nat.div_eq_of_lt_le (by linarith) (by rw [Nat.succ_mul]; linarith)
      · rw [if_neg hj10] at h1
        nlinarith
  · rw [dif_neg hp, ownMap_lane B π ch]
    have hp2 := p.2
    unfold wO at hp2
    have hpos : 0 < wE l.length := by unfold wE; omega
    have he : (p.val - 10 * wB l.length) / wE l.length < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
    by_cases hje : 10 ≤ j ∧ (p.val - 10 * wB l.length) / wE l.length = j - 10
    · obtain ⟨hj10, hej⟩ := hje
      have hloc : (p.val - 10 * wB l.length) % wE l.length < wE l.length := Nat.mod_lt _ hpos
      have hlo : p.val - (10 * wB l.length + (j - 10) * wE l.length) = (p.val - 10 * wB l.length) % wE l.length := by
        have := Nat.div_add_mod (p.val - 10 * wB l.length) (wE l.length); rw [hej] at this; rw [mul_comm] at this; omega
      have hin' : stOf l.length j ≤ p.val ∧ p.val < stOf l.length j + (if j < 10 then wB l.length else wE l.length) := by
        unfold stOf
        rw [if_neg (by omega), if_neg (by omega)]
        obtain ⟨q, hq⟩ : ∃ q, p.val = 10 * wB l.length + q := ⟨p.val - 10 * wB l.length, by omega⟩
        rw [hq, Nat.add_sub_cancel_left] at hej hloc
        have hdm := Nat.div_add_mod q (wE l.length)
        rw [hej, mul_comm] at hdm
        rw [hq]
        generalize (j - 10) * wE l.length = A at hdm ⊢
        generalize q % wE l.length = R at hdm hloc
        constructor <;> omega
      rw [if_pos hin']
      unfold stOf
      rw [if_neg (by omega), hlo]
      have htrace : pureTrace B ((mkSrc j r k : M K F)) ⟨27 + (p.val - 10 * wB l.length) / wE l.length, by omega⟩ =
          balWord 0 r (Mask.towerBasis B k) := by
        unfold mkSrc
        rw [dif_neg (by omega)]
        by_cases h10 : j = 10
        · rw [if_pos h10]
          have e27 : (⟨27 + (p.val - 10 * wB l.length) / wE l.length, by omega⟩ : Fin 29) = 27 :=
            Fin.ext (show 27 + (p.val - 10 * wB l.length) / wE l.length = 27 by omega)
          rw [e27]; exact pureTrace_gSrc B r k hr
        · rw [if_neg h10]
          have e28 : (⟨27 + (p.val - 10 * wB l.length) / wE l.length, by omega⟩ : Fin 29) = 28 :=
            Fin.ext (show 27 + (p.val - 10 * wB l.length) / wE l.length = 28 by omega)
          rw [e28]; exact pureTrace_dSrc B r k hr
      rw [htrace]
      exact hE hj10 _ ⟨(p.val - 10 * wB l.length) % wE l.length, hloc⟩
    · have hz : pureTrace B ((mkSrc j r k : M K F)) ⟨27 + (p.val - 10 * wB l.length) / wE l.length, by omega⟩ = 0 := by
        unfold mkSrc
        by_cases hj10 : j < 10
        · rw [dif_pos hj10]
          exact pureTrace_maskOnlySrc_other B ⟨j, hj10⟩ r _ (fun h => by
            have : 27 + (p.val - 10 * wB l.length) / wE l.length = 16 + j := congrArg Fin.val h
            generalize (p.val - 10 * wB l.length) / wE l.length = X at this
            omega)
        · rw [dif_neg hj10]
          by_cases h10 : j = 10
          · rw [if_pos h10]; exact pureTrace_gSrc_other B r k _ (fun h => hje ⟨by omega, by
              have : 27 + (p.val - 10 * wB l.length) / wE l.length = 27 := congrArg Fin.val h
              omega⟩)
          · rw [if_neg h10]; exact pureTrace_dSrc_other B r k _ (fun h => hje ⟨by omega, by
              have : 27 + (p.val - 10 * wB l.length) / wE l.length = 28 := congrArg Fin.val h
              omega⟩)
      rw [hz, map_zero, flatH1_zero B hB, if_neg, map_zero]
      intro ⟨h1, h2⟩
      unfold stOf at h1 h2
      by_cases hj10 : j < 10
      · rw [if_pos hj10] at h1 h2
        rw [if_pos hj10] at h2
        have : j * wB l.length + wB l.length ≤ 10 * wB l.length := by nlinarith
        omega
      · rw [if_neg hj10] at h1 h2
        rw [if_neg hj10] at h2
        apply hje ⟨by omega, ?_⟩
        obtain ⟨q, hq⟩ : ∃ q, p.val = 10 * wB l.length + q := ⟨p.val - 10 * wB l.length, by omega⟩
        rw [hq, Nat.add_sub_cancel_left]
        rw [hq] at h1 h2
        exact Nat.div_eq_of_lt_le (by linarith) (by rw [Nat.succ_mul]; linarith)

#print axioms limbs_zero
#print axioms flatC1_zero
#print axioms own_src_ident

end R1Z.CertOwn

end
