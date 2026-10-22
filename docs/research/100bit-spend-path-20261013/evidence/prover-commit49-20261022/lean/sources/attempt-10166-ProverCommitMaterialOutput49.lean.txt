import R1Z.ProverCommitMaterialFill49
/-! Complete 1024-cell materialization and exact kappa-weighted row values. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaterialOutput49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitWeightSum49
open ProverCommitMaterialFill49
open scoped BigOperators

theorem all (kp : Nat → Raw) (hkp : ∀ i, i<7 → canonical (kp i)) (raw : Nat → Nat → Old.Q) :
    ∃ out : Nat → Raw,
      materialization.all (sourceArray 7#usize kp) (table raw)=ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=terms kp (raw j.val) 7 0 := by
  obtain ⟨out,hout,hcout,hdout⟩ := fill kp hkp raw 1024 (fun _ => ProverCommitGamma48.zero)
    (fun _ _ => ProverCommitGamma48.zero_canonical) 0#usize 1024#u16 rfl (by decide)
  refine ⟨out,?_,hcout,?_⟩
  · rw [materialization.all,ProverCommitGamma48.repeat_zero]
    exact hout
  · intro j
    rw [hdout j.val j.isLt,if_pos (by have := j.isLt;change 0 ≤ j.val ∧ j.val<0+1024;omega),
      ProverCommitGamma48.zero_value,zero_add]

def run (x : Source) (raw : Array (Array field.QM31 7#usize) 1024#usize) :
    Result (Array Source 1024#usize) := do
  let kp ← kappa x
  materialization.all kp raw

theorem kappa_all (x : Raw) (hx : canonical x) (raw : Nat → Nat → Old.Q) :
    ∃ out : Nat → Raw, run (source x) (table raw)=ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=∑ k : Fin 7, value x^k.val*
        ProverCommitWideQM31Scalar49.embed (AspisR1.ExtractedCurrentQM31Exact.decode (raw j.val k.val)) := by
  obtain ⟨kp,hkp,hckp,hdpk⟩ := ProverCommitGamma48.kappa_exact x hx
  obtain ⟨out,hout,hcout,hdout⟩ := all kp hckp raw
  refine ⟨out,?_,hcout,?_⟩
  · simp only [run,hkp,hout,bind_tc_ok]
  · intro j
    rw [hdout j,ProverCommitWeightOutput49.terms_powers kp (raw j.val) (value x) hdpk 7 0 (by decide)]
    simp only [Nat.zero_add]

#print axioms all
#print axioms kappa_all
end R1Z.ProverCommitMaterialOutput49
