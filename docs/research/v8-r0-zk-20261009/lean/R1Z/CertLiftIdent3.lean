import R1Z.CertLiftIdent2

/-! D59.2 builder 2, part B: every extracted C1 / H1 lift entry is `φ` of the
`flatC1` / `flatH1` coordinate of the Lean lift source (`c1_entry_ident`,
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

theorem psi_diff (q1 q2 : A4) (b : ZP) :
    ψa B φ q1 - embR φ b * ψa B φ q2 = pack4 B (fun l => ((φ (ga q1 l.val - b * ga q2 l.val) : F) : K)) := by
  simp only [ψa, ψ4, pack4, embR, RingHom.coe_comp, Function.comp_apply, Subfield.coe_subtype, map_sub,
    map_mul, Subfield.coe_sub, Subfield.coe_mul, f0, f1, f2, f3]
  ring

theorem tb_eq (k : Fin 4) : tb B k.val = Mask.towerBasis B k := by
  unfold tb Mask.towerBasis
  rcases (by omega : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3) with h | h | h | h <;> simp [h]

theorem diff_eq (x y z : K) (b : ZP) (p : Prop) [Decidable p]
    (hb : embR (K := K) φ b = if p then 1 else 0) : x - (if p then z else 0) = x - embR φ b * z := by
  rw [hb]; split_ifs <;> ring

variable {Bat : Type} [BatchedLayer K Bat]

/-- **C1 entry identification.** -/
theorem c1_entry_ident (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
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
    (r : Fin 1024) (hr : r ≠ 1023) (rr ii : Usize) (hrr : rr.val = r.val)
    (i : Fin (24 + 4 * l.length)) (hii : ii.val = i.val) {v : U32}
    (hv : R1CertBuild.c1_entry al zz tr sx sy inact rr ii = ok v) :
    flatC1 B hB l (obs (Bat := Bat) π B ch c (c1Src r)) i = φ (v.val : ZP) := by
  obtain ⟨o1, o2, h1, h2', hvv⟩ := c1_entry_spec al zz tr sx sy inact hv
  obtain ⟨dd, h2, hdd⟩ : ∃ dd : Usize, R1CertBuild.c1_val al zz tr sx sy dd ii = ok o2 ∧ dd.val = 1023 :=
    ⟨_, h2', by simp⟩
  rw [hrr] at hvv
  have hfl := embR_flag φ inact r (hin r)
  unfold flatC1
  by_cases hi : i.val < 24
  · rw [dif_pos hi, flatHead_c1 B hB π ch c r hr i.val hi]
    obtain ⟨q1, hq1, e1⟩ := c1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h1
    obtain ⟨q2, hq2, e2⟩ := c1_val_head B φ al zz tr sx sy hT (by rw [hii]; exact hi) h2
    rw [hrr, hii, head_eq B φ π ch al zz tr ha hzx hzy htr r (i.val / 4) (by omega)] at hq1
    rw [hdd, hii, show (1023 : ℕ) = ((1023 : Fin 1024) : ℕ) from rfl,
      head_eq B φ π ch al zz tr ha hzx hzy htr 1023 (i.val / 4) (by omega)] at hq2
    rw [← hq1, ← hq2, diff_eq φ (ψa B φ q1) (ψa B φ q2) (ψa B φ q2) (gs inact r.val) _ hfl,
      limb_diff B φ hB q1 q2, hvv, e1, e2, hii]
  · rw [dif_neg hi]
    have hm : i.val - 24 < 4 * l.length := by omega
    have hql : l.get ⟨(i.val - 24) / 4, by omega⟩ ∈ ch.queries := by
      rw [hq, List.mem_toFinset]; exact List.get_mem _ _
    unfold c1Src
    rw [obs_balWord_opened (Bat := Bat) B π ch c 1023 r hr 1 _ _ hql]
    obtain ⟨q1, hq1, e1⟩ := c1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h1
    obtain ⟨q2, hq2, e2⟩ := c1_val_open B φ al zz tr sx sy hT (by rw [hii]; omega) h2
    rw [hii, hsx _ hm, hsy _ hm, hrr, show gN tr r.val = (π r).val from htr r, ev_eq] at hq1
    rw [hii, hsx _ hm, hsy _ hm, hdd, show (1023 : ℕ) = ((1023 : Fin 1024) : ℕ) from rfl,
      show gN tr ((1023 : Fin 1024) : ℕ) = (π 1023).val from htr 1023, ev_eq] at hq2
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

#print axioms psi_diff
#print axioms c1_entry_ident

end R1Z.CertBuild
