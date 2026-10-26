import R1Z.PV_L2_F3Adaptive
import R1Z.ProverCommitWordCarrier

/-! The rejection-preserving permutation on the actual 32-bit Word carrier.
High bits are retained; the two rejected u32s are fixed. This gives an exact
source-value map with the existing ProverCommitWordCarrier.accepted decoder. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3WordCarrier
open R1Z.PV_L2_F3Words R1Z.CommitReadsR1 R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable

def splitWord : Word ≃ Fin 2 × Candidate where
  toFun w := (⟨w.val / 2147483648, by have := w.isLt; change w.val < 4294967296 at this; omega⟩,
    ⟨w.val % 2147483648, by omega⟩)
  invFun p := ⟨p.1.val * 2147483648 + p.2.val, by
    have := p.1.isLt; have := p.2.isLt
    change p.1.val * 2147483648 + p.2.val < 4294967296
    omega⟩
  left_inv w := by apply Fin.ext; dsimp only; omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp only
    · have := p.1.isLt; have := p.2.isLt; omega
    · have := p.1.isLt; have := p.2.isLt; omega

def wordEquiv (e : Fin 2147483647 ≃ Fin 2147483647) : Word ≃ Word :=
  splitWord.trans ((Equiv.prodCongr (Equiv.refl (Fin 2)) (permute e)).trans splitWord.symm)

theorem split_permute (e : Fin 2147483647 ≃ Fin 2147483647) (w : Word) :
    splitWord (wordEquiv e w) = ((splitWord w).1,permute e (splitWord w).2) := by
  simp only [wordEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Equiv.refl_apply]
  rfl

theorem high_bit_preserved (e : Fin 2147483647 ≃ Fin 2147483647) (w : Word) :
    (wordEquiv e w).val / 2147483648 = w.val / 2147483648 :=
  congrArg (fun p : Fin 2 × Candidate => p.1.val) (split_permute e w)

theorem rejection_preserved (e : Fin 2147483647 ≃ Fin 2147483647) (w : Word) :
    rejB (wordEquiv e w) = rejB w := by
  apply Bool.eq_iff_iff.mpr
  rw [rejB_iff,rejB_iff]
  have hh := accepts_permute e (splitWord w).2
  have hs := congrArg (fun p : Fin 2 × Candidate => p.2) (split_permute e w)
  change (splitWord (wordEquiv e w)).2.val = 2147483647 ↔
    (splitWord w).2.val = 2147483647
  rw [hs]
  dsimp only
  have ha := (splitWord w).2.isLt
  have hb := (permute e (splitWord w).2).isLt
  change (splitWord w).2.val < 2147483648 at ha
  change (permute e (splitWord w).2).val < 2147483648 at hb
  unfold accepts at hh
  constructor
  · intro h
    have hnot : ¬ (permute e (splitWord w).2).val < 2147483647 := by omega
    have hn : ¬ (splitWord w).2.val < 2147483647 := fun h => hnot (hh.mpr h)
    omega
  · intro h
    have hnot : ¬ (splitWord w).2.val < 2147483647 := by omega
    have hn : ¬ (permute e (splitWord w).2).val < 2147483647 := fun h => hnot (hh.mp h)
    omega

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

def fieldPermute (e : Fin 2147483647 ≃ Fin 2147483647) : sourceBase (K := K) ≃ sourceBase (K := K) :=
  (baseEquiv (K := K)).symm.trans (e.trans (baseEquiv (K := K)))

theorem accepted_permute (e : Fin 2147483647 ≃ Fin 2147483647) (w : Word) :
    accepted (K := K) (wordEquiv e w) = (accepted (K := K) w).map (fieldPermute e) := by
  have hs := congrArg (fun p : Fin 2 × Candidate => p.2) (split_permute e w)
  by_cases hc : accepts (splitWord w).2
  · have hc' := (accepts_permute e (splitWord w).2).mpr hc
    have hmod : (wordEquiv e w).val % 2147483648 =
        (e ⟨(splitWord w).2.val,hc⟩).val := by
      change (splitWord (wordEquiv e w)).2.val = _
      rw [hs]
      change (splitWord w).2.val < 2147483647 at hc
      simp only [permute,Equiv.trans_apply,cellEquiv,dif_pos hc,
        Equiv.optionCongr_apply,Option.map_some,Equiv.symm_mk,Equiv.coe_fn_mk]
    have hgood : (wordEquiv e w).val % 2^31 < AspisCircleGroupOrder.P := by
      change (splitWord (wordEquiv e w)).2.val < 2147483647
      rw [hs]; exact hc'
    have hgood0 : w.val % 2^31 < AspisCircleGroupOrder.P := hc
    unfold accepted
    simp only [dif_pos hgood0, dif_pos hgood, Option.map_some]
    apply congrArg some
    apply (baseEquiv (K := K)).symm.injective
    simp only [fieldPermute,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
    apply Fin.ext
    exact hmod
  · have hf : accepted (K := K) w = none := by
      exact (accepted_failure w).mpr ((rejB_iff w).mpr (by
        change ¬ w.val % 2147483648 < 2147483647 at hc
        have hm := Nat.mod_lt w.val (by decide : 0 < 2147483648)
        change w.val % 2147483648 = 2147483647
        omega))
    rw [hf,Option.map_none]
    apply (accepted_failure _).mpr
    rw [rejection_preserved]
    exact (accepted_failure w).mp hf

#print axioms splitWord
#print axioms split_permute
#print axioms high_bit_preserved
#print axioms rejection_preserved
#print axioms accepted_permute
end R1Z.PV_L2_F3WordCarrier
