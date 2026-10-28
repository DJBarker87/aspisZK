import R1Z.ProverRw18ContextTotal
import R1Z.ProverCommitScale50
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldMeaning
open Aeneas Aeneas.Std Result
abbrev Raw := ProverCommitPrimitive47.Old.Q
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev K := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
abbrev Canonical := ProverCommitSubfieldOps47.Canonical
abbrev decode := AspisR1.ExtractedCurrentQM31Exact.decode

def full (x : Raw) : Q :=
  ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x)

theorem add (x y : Raw) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Raw, ProverRwDictionaryTower.qAdd (full x) (full y)=ok (full z) ∧
      Canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.add x y hx hy
  refine ⟨z,?_,hc,hd⟩
  simp only [ProverRwDictionaryTower.qAdd,full,
    ProverRwDictionaryTower.native_q_roundtrip,hz,ProverRwDictionaryTower.mapResult]

theorem mul (x y : Raw) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Raw, ProverRwDictionaryTower.qMul (full x) (full y)=ok (full z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.mul x y hx hy
  refine ⟨z,?_,hc,hd⟩
  simp only [ProverRwDictionaryTower.qMul,full,
    ProverRwDictionaryTower.native_q_roundtrip,hz,ProverRwDictionaryTower.mapResult]

theorem scale (x : Raw) (s : U32) :
    ∃ z : Raw, ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
      (AspisR1ProducerRelease47.field.QM31.mul_m31 (ProverRwDictionaryTower.toQ (full x)) s)=
        ok (full z) ∧ Canonical z ∧ decode z=decode x*(s.val : K) := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitScale50.scale x s
  refine ⟨z,?_,hc,hd⟩
  simp only [full,ProverRwDictionaryTower.native_q_roundtrip,hz,ProverRwDictionaryTower.mapResult]

#print axioms add
#print axioms mul
#print axioms scale
end R1Z.ProverRw18FieldMeaning
