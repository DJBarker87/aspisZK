import R1Z.ProverCommitEncoderGenericExact54
import R1Z.ProverCommitEncoderQOps54
/-! Native M31/QM31 used-method specializations. Every unused trait field
is arbitrary; no local arithmetic or node/model image premise remains. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderSpecialized54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitArray49 ProverCommitEncoderGenericExact54

theorem m31_encode (unused : scalar.CodeField field.M31) (f : Nat → U32)
    (hf : ∀ i, i<1024 → ProverCommitM31Ops48.canonical (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ out : Nat → U32,
      generic54.encode_at (ProverCommitEncoderM31Ops54.ops unused) (array 1024#usize f) j=ok (array 4#usize out) ∧
      (∀ s, s<4 → ProverCommitM31Ops48.canonical (out s)) ∧
      ∀ s : Fin 4, ProverCommitM31Ops48.decode (out s.val)=AspisWide.InitialEncoder.exactInitialEncoder
        (fun i => ProverCommitM31Ops48.decode (f i.val)) (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) := by
  exact encode_result _ _ _ _ (ProverCommitEncoderM31Ops54.arithmetic unused)
    (ProverCommitEncoderM31Ops54.sub_success unused) (by intro m hm;rfl) f hf j u hj

theorem qm31_encode (unused : scalar.CodeField field.QM31) (f : Nat → field.QM31)
    (hf : ∀ i, i<1024 → ProverCommitEncoderQOps54.valid (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ out : Nat → field.QM31,
      generic54.encode_at (ProverCommitEncoderQOps54.ops unused) (array 1024#usize f) j=ok (array 4#usize out) ∧
      (∀ s, s<4 → ProverCommitEncoderQOps54.valid (out s)) ∧
      ∀ s : Fin 4, ProverCommitEncoderQOps54.value (out s.val)=AspisWide.InitialEncoder.exactInitialEncoder
        (fun i => ProverCommitEncoderQOps54.value (f i.val)) (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) := by
  exact encode_result _ _ _ _ (ProverCommitEncoderQOps54.arithmetic unused)
    (ProverCommitEncoderQOps54.sub_success unused) (by intro m hm;rfl) f hf j u hj

theorem m31_eval (unused : scalar.CodeField field.M31) (f : Nat → U32)
    (hf : ∀ i, i<256 → ProverCommitM31Ops48.canonical (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ z : U32, generic54.eval_at (ProverCommitEncoderM31Ops54.ops unused)
      (Array.to_slice (array 256#usize f)) j 8#usize=ok z ∧ ProverCommitM31Ops48.canonical z ∧
      ProverCommitM31Ops48.decode z=AspisWide.FinalEncoder.exactFinalEncoder
        (fun i => ProverCommitM31Ops48.decode (f i.val)) u := by
  exact eval_result _ _ _ _ (ProverCommitEncoderM31Ops54.arithmetic unused) (by intro m hm;rfl) f hf j u hj

theorem qm31_eval (unused : scalar.CodeField field.QM31) (f : Nat → field.QM31)
    (hf : ∀ i, i<256 → ProverCommitEncoderQOps54.valid (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ z : field.QM31, generic54.eval_at (ProverCommitEncoderQOps54.ops unused)
      (Array.to_slice (array 256#usize f)) j 8#usize=ok z ∧ ProverCommitEncoderQOps54.valid z ∧
      ProverCommitEncoderQOps54.value z=AspisWide.FinalEncoder.exactFinalEncoder
        (fun i => ProverCommitEncoderQOps54.value (f i.val)) u := by
  exact eval_result _ _ _ _ (ProverCommitEncoderQOps54.arithmetic unused) (by intro m hm;rfl) f hf j u hj

#print axioms m31_encode
#print axioms qm31_encode
#print axioms m31_eval
#print axioms qm31_eval
end R1Z.ProverCommitEncoderSpecialized54
