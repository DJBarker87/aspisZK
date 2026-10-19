import R1Z.CertLiftIdent3

/-! D59.2 builder 2, part B (H1): each extracted H1 lift entry is `φ` of the
`flatH1` coordinate of `obs (h1Src r k)` (`h1_entry_ident`). -/

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

/-- `flatHead` of a balanced H1 word. -/
theorem flatHead_h1 (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (r : Fin 1024) (hr : r ≠ 0) (k : Fin 4) (i : ℕ) (hi : i < 24) :
    flatHead B hB (obs (Bat := Bat) π B ch 26 (h1Src B r k)) i hi =
      limbs B hB (tb B k.val * cellK π ch r (i / 4) -
        (if r ∈ copyInactiveRows then tb B k.val * cellK π ch 0 (i / 4) else 0)) ⟨i % 4, by omega⟩ := by
  unfold flatHead h1Src
  rw [tb_eq]
  by_cases h12 : i < 12
  · rw [dif_pos h12, obs_balWord_claim (Bat := Bat) B π ch 26 0 r hr,
      cellK_claim π ch r (i / 4) (by omega), cellK_claim π ch 0 (i / 4) (by omega)]
  · rw [dif_neg h12]
    by_cases h16 : i < 16
    · rw [dif_pos h16, obs_balWord_extra (Bat := Bat) B π ch 26 0 r hr,
        show i / 4 = 3 by omega, cellK_extra, cellK_extra]
      have hk : (⟨i - 12, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      rw [hk]
    · rw [dif_neg h16, obs_balWord_ood (Bat := Bat) B π ch 26 0 r hr]
      have hk : (⟨(i - 16) % 4, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      have hg : i / 4 = 4 + (⟨(i - 16) / 4, by omega⟩ : Fin 2).val := by simp; omega
      rw [hk, hg, cellK_ood, cellK_ood]

/-- **H1 entry identification.** -/
theorem h1_entry_ident (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
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
    flatH1 B hB l (obs (Bat := Bat) π B ch 26 (h1Src B r k)) i = φ (v.val : ZP) := by
  obtain ⟨o1, o2, h1, h2', hvv⟩ := h1_entry_spec al zz tr sx sy inact hv
  obtain ⟨dd, h2, hdd⟩ : ∃ dd : Usize, R1CertBuild.h1_val al zz tr sx sy dd kk ii = ok o2 ∧ dd.val = 0 :=
    ⟨_, h2', by simp⟩
  rw [hrr] at hvv
  have hfl := embR_flag φ inact r (hin r)
  unfold flatH1
  by_cases hi : i.val < 24
  · rw [dif_pos hi, flatHead_h1 B hB π ch r hr k i.val hi]
    obtain ⟨q1, hq1, e1⟩ := h1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h1
    obtain ⟨q2, hq2, e2⟩ := h1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h2
    rw [hrr, hii, hkk, head_eq B φ π ch al zz tr ha hzx hzy htr r (i.val / 4) (by omega)] at hq1
    rw [hdd, hii, hkk, show (0 : ℕ) = ((0 : Fin 1024) : ℕ) from rfl,
      head_eq B φ π ch al zz tr ha hzx hzy htr 0 (i.val / 4) (by omega)] at hq2
    rw [← hq1, ← hq2, diff_eq φ (ψa B φ q1) (ψa B φ q2) (ψa B φ q2) (gs inact r.val) _ hfl,
      limb_diff B φ hB q1 q2, hvv, e1, e2, hii]
  · rw [dif_neg hi]
    have hm : 4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4 < 4 * l.length := by omega
    have e4 : (4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4) / 4 = (i.val - 24) / 16 := by omega
    have e5 : (4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4) % 4 = (i.val - 24) % 16 / 4 := by omega
    have hql : l.get ⟨(i.val - 24) / 16, by omega⟩ ∈ ch.queries := by
      rw [hq, List.mem_toFinset]; exact List.get_mem _ _
    unfold h1Src
    rw [obs_balWord_opened (Bat := Bat) B π ch 26 0 r hr _ _ _ hql, ← tb_eq]
    obtain ⟨q1, hq1, e1⟩ := h1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h1
    obtain ⟨q2, hq2, e2⟩ := h1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h2
    have hX : ∀ m (hm' : m = 4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4),
        embR φ (gs sx m) = storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex
          (l.get ⟨(i.val - 24) / 16, by omega⟩) ⟨(i.val - 24) % 16 / 4, by omega⟩) := by
      intro m hm'
      rw [hsx m (by omega)]
      congr 3 <;> simp [hm', e4, e5]
    have hY : ∀ m (hm' : m = 4 * ((i.val - 24) / 16) + (i.val - 24) % 16 / 4),
        embR φ (gs sy m) = storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex
          (l.get ⟨(i.val - 24) / 16, by omega⟩) ⟨(i.val - 24) % 16 / 4, by omega⟩) := by
      intro m hm'
      rw [hsy m (by omega)]
      congr 3 <;> simp [hm', e4, e5]
    rw [hii, hkk, hX _ rfl, hY _ rfl, hrr, show gN tr r.val = (π r).val from htr r, ev_eq] at hq1
    rw [hii, hkk, hX _ rfl, hY _ rfl, hdd, show (0 : ℕ) = ((0 : Fin 1024) : ℕ) from rfl,
      show gN tr ((0 : Fin 1024) : ℕ) = (π 0).val from htr 0, ev_eq] at hq2
    rw [← hq1, ← hq2, diff_eq φ (ψa B φ q1) (ψa B φ q2) (ψa B φ q2) (gs inact r.val) _ hfl,
      limb_diff B φ hB q1 q2, hvv, e1, e2, hii]

#print axioms flatHead_h1
#print axioms h1_entry_ident

end R1Z.CertBuild
