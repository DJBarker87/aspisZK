import R1Z.PV_Inv_NativeQ
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativeNormQ
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem norm_operand (x : Old.Q) (hx : Canonical x) (hn : decode x ≠ 0) :
    ∃ a b r n : Old.C,
      field.CM31.square (ProverCommitNativeC49.source x.c0) = ok (ProverCommitNativeC49.source a) ∧
      field.CM31.square (ProverCommitNativeC49.source x.c1) = ok (ProverCommitNativeC49.source b) ∧
      kernels.mul_r (ProverCommitNativeC49.source b) = ok (ProverCommitNativeC49.source r) ∧
      field.CM31.sub (ProverCommitNativeC49.source a) (ProverCommitNativeC49.source r) = ok (ProverCommitNativeC49.source n) ∧
      ProverCommitNativeC49.Canonical n ∧ ProverCommitNativeC49.value n ≠ 0 := by
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitNativeSquare49.square x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitNativeSquare49.square x.c1 hx.2
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitNativeC49.mul_r b hcb
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverCommitNativeC49.sub a r hca hcr
  refine ⟨a,b,r,n,ha,hb,hr,hnn,hcn,?_⟩
  have hnorm : ProverCommitNativeC49.value n = QuadraticAlgebra.norm (decode x) := by
    rw [hvn,hva,hvr,hvb,ProverCommitNativeQInverse49.norm_value]
    change ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-qm31R*(ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1) = ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-qm31R*ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1
    ring
  intro hz
  exact hn (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (hnorm.symm.trans hz))

#print axioms norm_operand
end R1Z.PV_Inv_NativeNormQ
