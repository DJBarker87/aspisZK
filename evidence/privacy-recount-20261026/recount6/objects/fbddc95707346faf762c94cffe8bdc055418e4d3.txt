import R1Z.ProverRwSuccessComplexOperations
import R1Z.ProverCommitNativeQInverse49
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessQuarticInverseExact
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)
abbrev input (x : Old.Q) : ProverRwDictionaryTower.Q :=
  ⟨ProverRwSuccessComplexInverseExact.input x.c0,ProverRwSuccessComplexInverseExact.input x.c1⟩
abbrev r : Old.C := ⟨2#u32,1#u32⟩
theorem r_canonical : ProverCommitNativeC49.Canonical r := by constructor <;> decide
theorem r_value : ProverCommitNativeC49.value r=qm31R := rfl
variable [ExternalTypes]

theorem inverse (ops : ExternalFuns) (x : Old.Q) (hx : Canonical x) (hn : decode x≠0) :
    ∃ z : Old.Q, (ProverRwSuccessInverseInstall.selected ops).op107 (input x)=.ok (some (input z)) ∧
      Canonical z ∧ decode z=(decode x)⁻¹ := by
  obtain ⟨a,ha,hca,hva⟩ := ProverRwSuccessComplexOperations.mul x.c0 x.c0 hx.1 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverRwSuccessComplexOperations.mul x.c1 x.c1 hx.2 hx.2
  obtain ⟨rb,hrb,hcrb,hvrb⟩ := ProverRwSuccessComplexOperations.mul r b r_canonical hcb
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverRwSuccessComplexOperations.sub a rb hca hcrb
  have hnorm : ProverCommitNativeC49.value n=QuadraticAlgebra.norm (decode x) := by
    rw [hvn,hva,hvrb,hvb,r_value,ProverCommitNativeQInverse49.norm_value]
    change ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-
      qm31R*(ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1)=
      ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-
      qm31R*ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1
    ring
  have nonzero : ProverCommitNativeC49.value n≠0 := by
    intro he;apply hn
    exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (hnorm.symm.trans he)
  obtain ⟨ni,hni,hcni,hvni⟩ := ProverRwSuccessComplexInverseExact.inverse ops n hcn nonzero
  obtain ⟨lo,hlo,hclo,hvlo⟩ := ProverRwSuccessComplexOperations.mul x.c0 ni hx.1 hcni
  obtain ⟨nb,hnb,hcnb,hvnb⟩ := ProverRwSuccessComplexOperations.neg x.c1 hx.2
  obtain ⟨hi,hhi,hchi,hvhi⟩ := ProverRwSuccessComplexOperations.mul nb ni hcnb hcni
  unfold ProverRwSuccessComplexOperations.S.mul ProverRwSuccessComplexOperations.input at ha hb hrb hlo hhi
  unfold ProverRwSuccessComplexOperations.S.sub ProverRwSuccessComplexOperations.input at hnn
  unfold ProverRwSuccessComplexOperations.S.neg ProverRwSuccessComplexOperations.input at hnb
  unfold ProverRwSuccessInverseTotal.Src.cInv at hni
  refine ⟨⟨lo,hi⟩,?_,⟨hclo,hchi⟩,?_⟩
  · change ProverRwSuccessInverseInstall.Src.qInv (input x)=_
    unfold ProverRwSuccessInverseInstall.Src.qInv
      ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
    have cr : ProverRwSuccessInverseSource.field.CM31.new 2#u32
        ProverRwSuccessInverseSource.field.M31.ONE=.ok (ProverRwSuccessComplexInverseExact.input r) := rfl
    rw [cr]
    simp only [bind_tc_ok,input]
    rw [ha]
    simp only [bind_tc_ok]
    rw [hb]
    simp only [bind_tc_ok]
    rw [hrb]
    simp only [bind_tc_ok]
    rw [hnn]
    simp only [bind_tc_ok]
    rw [hni]
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    rw [hlo]
    simp only [bind_tc_ok]
    rw [hnb]
    simp only [bind_tc_ok]
    rw [hhi]
    rfl
  · rw [hnorm] at hvni
    apply QuadraticAlgebra.ext
    · change ProverCommitNativeC49.value lo=_
      rw [hvlo,hvni,QuadraticAlgebra.re_inv]
      simp only [zero_mul,add_zero]
      change ProverCommitNativeC49.value x.c0*(QuadraticAlgebra.norm (decode x))⁻¹=(QuadraticAlgebra.norm (decode x))⁻¹*ProverCommitNativeC49.value x.c0
      ring
    · change ProverCommitNativeC49.value hi=_
      rw [hvhi,hvnb,hvni,QuadraticAlgebra.im_inv]
      change -ProverCommitNativeC49.value x.c1*(QuadraticAlgebra.norm (decode x))⁻¹= -((QuadraticAlgebra.norm (decode x))⁻¹*ProverCommitNativeC49.value x.c1)
      ring
#print axioms r_canonical
#print axioms r_value
#print axioms inverse
end R1Z.ProverRwSuccessQuarticInverseExact
