import R1Z.ProverCommitMaskInventory51
/-! Actual coefficient-array producer, with no coefficient-image premise. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaskProducer51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitMaskSchedule51
variable {F : Subfield QM31Exact}

def word (i : Nat) : U8 := UScalar.ofNatCore (if h : i<26 then exponent i else 0) (by
  change (if h : i<26 then exponent i else 0)<256
  split_ifs with h
  · exact lt_trans (bound ⟨i,h⟩) (by decide)
  · decide)

theorem word_value (i : Nat) (hi : i<26) : (word i).val=exponent i := by
  simp only [word,UScalar.ofNatCore_val_eq,dif_pos hi]

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array
  ProverCommitMaskPolynomial50.polynomial ProverCommitWriteMath51.polynomial

theorem exact_result (B : R0P.PackBasis F)
    (hi : B.i=⟨ProverCommitTower50.ci,0⟩) (hu : B.u=⟨0,1⟩)
    (p : Nat → Old.Q) (hp : ∀ i, i<26 → Canonical (p i)) :
    ∃ q : Nat → Old.Q,
      mask_coeff51.eval (ProverCommitQArray48.array 26#usize p) (ProverCommitMaskWrites51.exponents word)=
        ok (ProverCommitQArray48.array 27#usize q) ∧
      (∀ k, k<27 → Canonical (q k)) ∧
      (∀ k, decode (q k)=(ProverCommitMaskPolynomial50.polynomial B
        (fun i : Fin 16 => decode (p i.val)) (fun i : Fin 10 => decode (p (16+i.val)))).coeff k) := by
  let c1 := fun i : Fin 16 => decode (p i.val)
  let mo := fun i : Fin 10 => decode (p (16+i.val))
  let v := fun i => ProverCommitTower50.basis ⟨i%4,Nat.mod_lt _ (by decide)⟩*decode (p i)
  let target := fun k => (ProverCommitMaskPolynomial50.polynomial B c1 mo).coeff k
  have hv (i : Nat) (hib : i<26) : v i=target (word i).val := by
    rw [word_value i hib]
    dsimp only [target]
    rw [←ProverCommitMaskInventory51.polynomial]
    rw [ProverCommitWriteMath51.coeff_at _ _ injective ⟨i,hib⟩]
    dsimp only [v,ProverCommitMaskInventory51.value]
    rw [ProverCommitTowerModel50.basis_model B hi hu]
    dsimp only [ProverCommitMaskInventory51.input,Fin.val_mk,c1,mo]
    split_ifs with h
    · rfl
    · have he : 16+(i-16)=i := by omega
      simp only [mo,he,R0P.Mask.mulTowerBasis]
  have hzero (k : Nat) (hk : ∀ i, 26 - 26 ≤ i → i<26 → (word i).val≠k) : decode zero=target k := by
    rw [zero_decode]
    dsimp only [target]
    rw [←ProverCommitMaskInventory51.polynomial]
    symm
    apply ProverCommitWriteMath51.coeff_outside
    intro i
    have h := hk i.val (by omega) i.isLt
    rw [word_value _ i.isLt] at h
    exact h
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitMaskWrites51.go p hp word
    (fun i hib => by rw [word_value _ hib];exact bound ⟨i,hib⟩)
    26 26#u8 rfl (by decide) (fun _ => zero) (fun _ _ => zero_canonical)
  refine ⟨q,?_,hcq,?_⟩
  · rw [mask_coeff51.eval,ProverCommitQArray48.repeat_zero]
    exact hq
  · have hfill := ProverCommitWriteMath51.fill_eq (fun i => (word i).val) v target hv 26 (by decide)
      (fun _ => decode zero) hzero
    rw [hfill] at hdq
    intro k
    exact congrFun hdq k

#print axioms word_value
#print axioms exact_result
end R1Z.ProverCommitMaskProducer51
