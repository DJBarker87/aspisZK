import R1Z.CertLiftIdent

/-! D59.2 builder 2, part B (C1): each extracted C1 lift entry is `φ` of the
`flatC1` coordinate of `obs (c1Src r)` (`c1_entry_ident`).  Inputs under named
premises (D59.2 ruling): `htr` (transport table = π), `hzx`/`hzy` (OOD points),
`hsx`/`hsy` (stored points of the opened pairs), `hin` (inactive flags =
`copyInactiveRows`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R0P.SemSource R1Z.RfChain R1Z.RfOwn R1Z.RfObs R1Z.RfSrc
open R0Z.K4 R0Z.HonestView AspisCircleTensorBinding R1Z.PredicateR1
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

theorem f0 : ((0 : Fin 4) : ℕ) = 0 := rfl
theorem f1 : ((1 : Fin 4) : ℕ) = 1 := rfl
theorem f2 : ((2 : Fin 4) : ℕ) = 2 := rfl
theorem f3 : ((3 : Fin 4) : ℕ) = 3 := rfl

/-- The `K₄` difference of two limb arrays has the limbwise difference as limbs. -/
theorem limb_diff (hB : PackField B) (q1 q2 : A4) (b : ZP) :
    limbs B hB (ψa B φ q1 - embR φ b * ψa B φ q2) = fun l => φ (ga q1 l.val - b * ga q2 l.val) := by
  have e : ψa B φ q1 - embR φ b * ψa B φ q2 = pack4 B (fun l => ((φ (ga q1 l.val - b * ga q2 l.val) : F) : K)) := by
    simp only [ψa, ψ4, pack4, embR, RingHom.coe_comp, Function.comp_apply, Subfield.coe_subtype, map_sub,
      map_mul, Subfield.coe_sub, Subfield.coe_mul, f0, f1, f2, f3]
    ring
  rw [e, limbs_pack4 B hB]

/-- A base-field `K₄` value has limb 0 equal to it. -/
theorem pack4_base (w : Fin 4 → F) (x : F) (h : pack4 B (fun l => (w l : K)) = (x : K)) : w 0 = x := by
  have hz : pack4 B (fun l => ((w l : K) - (if l = 0 then (x : K) else 0))) = 0 := by
    have : pack4 B (fun l => ((w l : K) - (if l = 0 then (x : K) else 0))) =
        pack4 B (fun l => (w l : K)) - (x : K) := by
      simp only [pack4]
      simp
      ring
    rw [this, h, sub_self]
  have := (pack4_eq_zero_iff B _ (fun j => by
    by_cases hj : j = 0
    · rw [if_pos hj]; exact F.sub_mem (w j).2 x.2
    · rw [if_neg hj, sub_zero]; exact (w j).2)).1 hz 0
  rw [if_pos rfl] at this
  exact Subtype.ext (sub_eq_zero.1 this)

theorem embR_flag (inact : Slice U32) (r : Fin 1024)
    (hin : gs inact r.val = if r ∈ copyInactiveRows then 1 else 0) :
    embR (K := K) φ (gs inact r.val) = if r ∈ copyInactiveRows then 1 else 0 := by
  rw [hin]; split_ifs <;> simp

theorem cellK_claim (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (r : Fin 1024) (g : ℕ) (hg : g < 3) :
    cellK π ch r g = rustEq (rustPoints (alpha ch) ⟨g, hg⟩) r := by
  unfold cellK; rw [dif_pos hg]

theorem cellK_extra (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (r : Fin 1024) :
    cellK π ch r 3 = rustHWeight (alpha ch) (π r) := by
  unfold cellK; rw [dif_neg (by norm_num), if_pos rfl]

theorem cellK_ood (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (r : Fin 1024) (j : Fin 2) :
    cellK π ch r (4 + j.val) = rustEvalRow (π r) (ch.circle j).1.1 (ch.circle j).1.2 := by
  unfold cellK
  rw [dif_neg (by omega), if_neg (by omega)]
  rcases (by omega : j.val = 0 ∨ j.val = 1) with h | h
  · have : j = 0 := Fin.ext h
    subst this
    rw [if_pos (by simp)]
  · have : j = 1 := Fin.ext h
    subst this
    rw [if_neg (by simp)]

variable {Bat : Type} [BatchedLayer K Bat]

/-- `flatHead` of a balanced C1 word: limb `i mod 4` of the cell `i / 4` difference. -/
theorem flatHead_c1 (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (c : Fin 29)
    (r : Fin 1024) (hr : r ≠ 1023) (i : ℕ) (hi : i < 24) :
    flatHead B hB (obs (Bat := Bat) π B ch c (c1Src r)) i hi =
      limbs B hB (cellK π ch r (i / 4) - (if r ∈ copyInactiveRows then cellK π ch 1023 (i / 4) else 0))
        ⟨i % 4, by omega⟩ := by
  unfold flatHead c1Src
  by_cases h12 : i < 12
  · rw [dif_pos h12, obs_balWord_claim (Bat := Bat) B π ch c 1023 r hr 1,
      cellK_claim π ch r (i / 4) (by omega), cellK_claim π ch 1023 (i / 4) (by omega)]
    simp only [one_mul]
  · rw [dif_neg h12]
    by_cases h16 : i < 16
    · rw [dif_pos h16, obs_balWord_extra (Bat := Bat) B π ch c 1023 r hr 1,
        show i / 4 = 3 by omega, cellK_extra, cellK_extra]
      have hk : (⟨i - 12, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      rw [hk]
      simp only [one_mul]
    · rw [dif_neg h16, obs_balWord_ood (Bat := Bat) B π ch c 1023 r hr 1]
      have hk : (⟨(i - 16) % 4, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp; omega)
      have hg : i / 4 = 4 + (⟨(i - 16) / 4, by omega⟩ : Fin 2).val := by simp; omega
      rw [hk, hg, cellK_ood, cellK_ood]
      simp only [one_mul]

#print axioms limb_diff
#print axioms pack4_base
#print axioms flatHead_c1

end R1Z.CertBuild
