import R1Z.CertOwnFill
import R1Z.CertLiftIdent4

/-! D62 builder 3: the extracted own entries are the Lean own coordinates of a
single lane word.  `own_c1_ident`: a mask-only own entry (C1 values balanced at
row 0) is `φ` of the `flatC1` coordinate of `obs (balWord 0 r 1)`;
`own_h1_ident`: a G/D own entry is `φ` of the `flatH1` coordinate of
`obs (balWord 0 r (towerBasis k))` in any lane (`obs_lane`, then
`h1_entry_ident`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R0P.SemSource R1Z.RfChain R1Z.RfOwn R1Z.RfObs R1Z.RfSrc
open R0Z.K4 R0Z.HonestView AspisCircleTensorBinding R1Z.PredicateR1
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

variable {Bat : Type} [BatchedLayer K Bat]

/-- A balanced lane word observes the same in every lane. -/
theorem obs_lane (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c c' : Fin 29) (d r : Fin 1024) (hr : r ≠ d)
    (x : K) : obs (Bat := Bat) π B ch c (balWord d r x) = obs (Bat := Bat) π B ch c' (balWord d r x) := by
  funext oc
  cases oc with
  | claim j => rw [obs_balWord_claim (Bat := Bat) B π ch c d r hr x, obs_balWord_claim (Bat := Bat) B π ch c' d r hr x]
  | extra => rw [obs_balWord_extra (Bat := Bat) B π ch c d r hr x, obs_balWord_extra (Bat := Bat) B π ch c' d r hr x]
  | ood j => rw [obs_balWord_ood (Bat := Bat) B π ch c d r hr x, obs_balWord_ood (Bat := Bat) B π ch c' d r hr x]
  | opened q s =>
    by_cases hq : q ∈ ch.queries
    · rw [obs_balWord_opened (Bat := Bat) B π ch c d r hr x q s hq,
        obs_balWord_opened (Bat := Bat) B π ch c' d r hr x q s hq]
    · rw [obs_opened_zero π B ch c _ q s hq, obs_opened_zero π B ch c' _ q s hq]

/-- `flatHead` of a balanced C1 word: limb `i mod 4` of the cell `i / 4` difference. -/
theorem flatHead_c1z (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (r : Fin 1024) (hr : r ≠ 0) (i : ℕ) (hi : i < 24) :
    flatHead B hB (obs (Bat := Bat) π B ch c (balWord 0 r 1)) i hi =
      limbs B hB (cellK π ch r (i / 4) - (if r ∈ copyInactiveRows then cellK π ch 0 (i / 4) else 0))
        ⟨i % 4, by omega⟩ := by
  unfold flatHead
  by_cases h12 : i < 12
  · rw [dif_pos h12, obs_balWord_claim (Bat := Bat) B π ch c 0 r hr 1,
      cellK_claim π ch r (i / 4) (by omega), cellK_claim π ch 0 (i / 4) (by omega)]
    simp only [one_mul]
  · rw [dif_neg h12]
    by_cases h16 : i < 16
    · rw [dif_pos h16, obs_balWord_extra (Bat := Bat) B π ch c 0 r hr 1,
        show i / 4 = 3 by omega, cellK_extra, cellK_extra]
      have hk : (⟨i - 12, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      rw [hk]
      simp only [one_mul]
    · rw [dif_neg h16, obs_balWord_ood (Bat := Bat) B π ch c 0 r hr 1]
      have hk : (⟨(i - 16) % 4, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      have hg : i / 4 = 4 + (⟨(i - 16) / 4, by omega⟩ : Fin 2).val := by simp; omega
      rw [hk, hg, cellK_ood, cellK_ood]
      simp only [one_mul]

/-- **Own C1 entry identification** (balanced at row 0). -/
theorem own_c1_ident (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (c : Fin 29) (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (al zz tr sx sy inact : Slice U32)
    (ha : ∀ (j : ℕ) (h : j < 10), Alimb B φ al j = alpha ch ⟨j, h⟩)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (ch.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (ch.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val)
    (hin : ∀ r : Fin 1024, gs inact r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hsx : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sx m) =
      storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hsy : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sy m) =
      storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (r : Fin 1024) (hr : r ≠ 0) (rr ii : Usize) (hrr : rr.val = r.val)
    (i : Fin (24 + 4 * l.length)) (hii : ii.val = i.val) {v : U32}
    (hv : R1CertBuild.own_c1 al zz tr sx sy inact rr ii = ok v) :
    flatC1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r 1)) i = φ (v.val : ZP) := by
  obtain ⟨o1, o2, h1, ⟨dd, hdd, h2⟩, hvv⟩ := own_c1_spec al zz tr sx sy inact hv
  rw [hrr] at hvv
  have hfl := embR_flag φ inact r (hin r)
  unfold flatC1
  by_cases hi : i.val < 24
  · rw [dif_pos hi, flatHead_c1z B hB π ch c r hr i.val hi]
    obtain ⟨q1, hq1, e1⟩ := c1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h1
    obtain ⟨q2, hq2, e2⟩ := c1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h2
    rw [hrr, hii, head_eq B φ π ch al zz tr ha hzx hzy htr r (i.val / 4) (by omega)] at hq1
    rw [hdd, hii, show (0 : ℕ) = ((0 : Fin 1024) : ℕ) from rfl,
      head_eq B φ π ch al zz tr ha hzx hzy htr 0 (i.val / 4) (by omega)] at hq2
    rw [← hq1, ← hq2, diff_eq φ (ψa B φ q1) (ψa B φ q2) (ψa B φ q2) (gs inact r.val) _ hfl,
      limb_diff B φ hB q1 q2, hvv, e1, e2, hii]
  · rw [dif_neg hi]
    have hm : i.val - 24 < 4 * l.length := by omega
    have hql : l.get ⟨(i.val - 24) / 4, by omega⟩ ∈ ch.queries := by
      rw [hq, List.mem_toFinset]; exact List.get_mem _ _
    rw [obs_balWord_opened (Bat := Bat) B π ch c 0 r hr 1 _ _ hql]
    obtain ⟨q1, hq1, e1⟩ := c1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h1
    obtain ⟨q2, hq2, e2⟩ := c1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h2
    rw [hii, hsx _ hm, hsy _ hm, hrr, show gN tr r.val = (π r).val from htr r, ev_eq] at hq1
    rw [hii, hsx _ hm, hsy _ hm, hdd, show (0 : ℕ) = ((0 : Fin 1024) : ℕ) from rfl,
      show gN tr ((0 : Fin 1024) : ℕ) = (π 0).val from htr 0, ev_eq] at hq2
    simp only [one_mul]
    rw [← hq1, ← hq2, diff_eq φ (ψa B φ q1) (ψa B φ q2) (ψa B φ q2) (gs inact r.val) _ hfl]
    have hmem : ψa B φ q1 - embR φ (gs inact r.val) * ψa B φ q2 ∈ F := by
      rw [hq1, hq2, hfl]
      refine F.sub_mem (rustEvalRow_mem F _ (algebraMap_mem F _) (algebraMap_mem F _)) ?_
      split_ifs
      · rw [one_mul]; exact rustEvalRow_mem F _ (algebraMap_mem F _) (algebraMap_mem F _)
      · rw [zero_mul]; exact F.zero_mem
    have hb := pack4_base B (fun l => φ (ga q1 l.val - gs inact r.val * ga q2 l.val))
      ⟨_, hmem⟩ (by rw [← psi_diff B φ q1 q2])
    rw [show limbF (ψa B φ q1 - embR φ (gs inact r.val) * ψa B φ q2) = ⟨_, hmem⟩ by
      unfold limbF; rw [dif_pos hmem], ← hb, hvv, e1, e2]
    simp

/-- **Own G/D entry identification** (any lane `c`). -/
theorem own_h1_ident (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (c : Fin 29) (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (al zz tr sx sy inact : Slice U32)
    (ha : ∀ (j : ℕ) (h : j < 10), Alimb B φ al j = alpha ch ⟨j, h⟩)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (ch.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (ch.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val)
    (hin : ∀ r : Fin 1024, gs inact r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hsx : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sx m) =
      storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hsy : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sy m) =
      storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (r : Fin 1024) (hr : r ≠ 0) (k : Fin 4) (rr kk ii : Usize) (hrr : rr.val = r.val) (hkk : kk.val = k.val)
    (i : Fin (24 + 16 * l.length)) (hii : ii.val = i.val) {v : U32}
    (hv : R1CertBuild.h1_entry al zz tr sx sy inact rr kk ii = ok v) :
    flatH1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r (Mask.towerBasis B k))) i = φ (v.val : ZP) := by
  rw [obs_lane (Bat := Bat) B π ch c 26 0 r hr]
  exact h1_entry_ident (Bat := Bat) B φ hT hB π ch l hq al zz tr sx sy inact ha hzx hzy htr hin hsx hsy
    r hr k rr kk ii hrr hkk i hii hv

#print axioms obs_lane
#print axioms flatHead_c1z
#print axioms own_c1_ident
#print axioms own_h1_ident

end R1Z.CertBuild
