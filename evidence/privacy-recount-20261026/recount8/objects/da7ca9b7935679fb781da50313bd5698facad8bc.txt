import R1Z.ProverCommitScalar48
/-! Canonical base-field operations for the interpolation denominator and
basis coefficients. No concrete denominator is normalized in the kernel. -/
set_option autoImplicit false
namespace R1Z.ProverCommitM31Ops48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev P : Nat := AspisCircleGroupOrder.P
abbrev M := ZMod P
abbrev canonical (x : U32) : Prop := x.val < P
abbrev decode := ProverCommitInverse48.decode

theorem mul_exact (x y : U32) :
    ∃ z : U32, field.M31.mul x y=ok z ∧ canonical z ∧ decode z=decode x*decode y :=
  ⟨ProverCommitInverse48.wordMul x y,ProverCommitInverse48.release_multiply x y,
    ProverCommitScalar48.word_canonical x y,ProverCommitInverse48.word_mul x y⟩

theorem add_exact (x y : U32) (hx : canonical x) (hy : canonical y) :
    ∃ z : U32, field.M31.add x y=ok z ∧ canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hval,hc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have checked : AspisR1ProducerChecked47.field.M31.add x y=ok z := by
    rw [ProverCommitPrimitive47.mAdd,hz]
  refine ⟨z,ProverCommitRelease47.mAdd x y z checked,hc,?_⟩
  change (z.val : M)=(x.val : M)+(y.val : M)
  rw [hval,ZMod.natCast_mod,Nat.cast_add]

theorem sub_exact (x y : U32) (hx : canonical x) (hy : canonical y) :
    ∃ z : U32, field.M31.sub x y=ok z ∧ canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨z,hz,hval,hc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  have checked : AspisR1ProducerChecked47.field.M31.sub x y=ok z := by
    rw [ProverCommitPrimitive47.mSub,hz]
  refine ⟨z,ProverCommitRelease47.mSub x y z checked,hc,?_⟩
  change (z.val : M)=(x.val : M)-(y.val : M)
  rw [hval]
  exact ProverCommitSubDecode47.limb_sub _ _ hy

#print axioms mul_exact
#print axioms add_exact
#print axioms sub_exact
end R1Z.ProverCommitM31Ops48
