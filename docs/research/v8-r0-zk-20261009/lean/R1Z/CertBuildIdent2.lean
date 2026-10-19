import R1Z.CertBuildIdent

/-! D57.3: **`chain_ident`** — the extracted `fill_tq` computes the Lean
ChainT0K4 targets: `chainTarget B hB a i t = φ (r[i·1084 + t])` given the
tower premise, the alpha limbs (`ha`) and `hinv · (a₉ - ½) = 1` (`hH`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.RfChain R0Z.K4
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

theorem embR_half : embR (K := K) φ 1073741824 = 1 / 2 := by
  have h2 : (2 * 1073741824 : ZP) = 1 := rfl
  have : (2 : K) * embR φ 1073741824 = 1 := by
    rw [← map_ofNat (embR (K := K) φ) 2, ← map_mul, h2, map_one]
  rw [one_div]
  exact eq_inv_of_mul_eq_one_right this

theorem phiF_ite (p : Prop) [Decidable p] : ((φ (if p then 1 else 0) : F) : K) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem pack4_lin (f g : Fin 4 → K) (z : K) :
    pack4 B (fun l => f l + z * g l) = pack4 B f + z * pack4 B g := by
  unfold pack4; ring

/-- **`chain_ident`**: the builder's `tq` is the Lean chain-target matrix. -/
theorem chain_ident (hT : Tower B) (hB : PackField B) (al hinv : Slice U32) (a : Fin 10 → K)
    (ha : ∀ j : Fin 10, Alimb B φ al j.val = a j) (hH : Hlimb B φ hinv * (a 9 - 1 / 2) = 1)
    {r : alloc.vec.Vec U32} (h : R1CertBuild.fill_tq al hinv = ok r) :
    ∀ i t : Fin 1084, chainTarget B hB a i t = φ (gs (alloc.vec.Vec.deref r) (i.val * 1084 + t.val)) := by
  intro i t
  obtain ⟨c, hc, hent⟩ := fill_tq_spec B φ hT h i.val i.2
  have hrt : gs (alloc.vec.Vec.deref r) (i.val * 1084 + t.val) = ent i.val c t.val := hent t.val t.2
  set V' : Fin 271 → K := unflatL B (fun t => if i = t then (1 : F) else 0) with hV'
  have hVV : ∀ (q : ℕ) (hq : q < 271), Vu B (i.val / 4) (i.val % 4) q = V' ⟨q, hq⟩ :=
    fun q hq => (unflat_unit B i ⟨q, hq⟩).symm
  have hA : ∀ (j : ℕ) (hj : j < 10), Alimb B φ al j = a ⟨j, hj⟩ := fun j hj => ha ⟨j, hj⟩
  have fv := finalVal_eq (Vu B (i.val / 4) (i.val % 4)) V' hVV (Alimb B φ al) a hA
  have hHi : Hlimb B φ hinv = (a 9 - 1 / 2)⁻¹ := eq_inv_of_mul_eq_one_left hH
  have hs : ψa B φ c = finalVal a V' * corr a := by
    rw [hc, corrK, fv, hHi, embR_half, corr]
    ring
  -- the coordinate and limb of t
  set q := (fpe.symm t).1 with hq
  set l := (fpe.symm t).2 with hl
  have ht : t.val = l.val + 4 * q.val := by
    have := fpe_val q l
    rw [show fpe (q, l) = t by rw [hq, hl]; exact fpe.apply_symm_apply t] at this
    exact this
  -- the limb vector of coordinate q
  let w : Fin 4 → F := fun l' => φ (ent i.val c (l'.val + 4 * q.val))
  have hw : ∀ l' : Fin 4, ((w l' : F) : K) =
      ((if i = fpe (q, l') then (1 : F) else 0 : F) : K) +
        (if q = idx 9 0 then 1 else 0) * embR φ (ga c l'.val) := by
    intro l'
    have hl4 := l'.2
    have e1 : (l'.val + 4 * q.val = i.val) ↔ (i = fpe (q, l')) := by rw [Fin.ext_iff, fpe_val]; omega
    have e2 : ((l'.val + 4 * q.val) / 4 = 244) ↔ (q = idx 9 0) := by
      rw [Fin.ext_iff, idx_nine_zero]; omega
    have e3 : (l'.val + 4 * q.val) % 4 = l'.val := by omega
    simp only [w, ent, map_add, map_mul, Subfield.coe_add, Subfield.coe_mul, e3]
    rw [phiF_ite, phiF_ite]
    simp only [e1, e2]
    by_cases hc1 : i = fpe (q, l') <;> simp [hc1, embR]
  have hval : RfChain.normalize a V' q = pack4 B (fun l' => ((w l' : F) : K)) := by
    rw [funext hw, pack4_lin]
    unfold RfChain.normalize
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ← hs, hV', unflatL_apply]
    congr 1
    · rw [mul_comm]
      congr 1
  unfold chainTarget flat
  have hn : RfChain.normalize a (unflatL B (fun j => if i = j then (1 : F) else 0)) (fpe.symm t).1 =
      RfChain.normalize a V' q := by rw [hV']
  rw [hn, hval, limbs_pack4 B hB w, hrt]
  show φ (ent i.val c (l.val + 4 * q.val)) = φ (ent i.val c t.val)
  rw [ht]

#print axioms embR_half
#print axioms chain_ident

end R1Z.CertBuild
