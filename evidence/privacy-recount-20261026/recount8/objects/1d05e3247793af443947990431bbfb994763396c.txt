import R1Z.ProverRwSuccessInverseInstall
import R1Z.ProverRwSuccessPowerExact
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessScalarInverseExact
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitM31Ops48

abbrev exponent : U64 := core.convert.num.FromU64U32.from
  (U32.wrapping_sub ProverRwSuccessInverseSource.field.P 2#u32)
theorem exponent_val : exponent.val=AspisCircleGroupOrder.P-2 := by
  unfold exponent ProverRwSuccessInverseSource.field.P AspisR1ProducerRelease47.field.P
  rfl

variable [ExternalTypes]
theorem exact_result (ops : ExternalFuns) (x : U32) (nonzero : x≠0#u32) :
    ∃ z : U32, (ProverRwSuccessInverseInstall.selected ops).op105 x=.ok (some z) ∧
      canonical z ∧ decode z=(decode x)⁻¹ := by
  obtain ⟨z,hz,hcz,hvz⟩ := ProverRwSuccessPowerExact.exact_result
    (AspisCircleGroupOrder.P-2) exponent exponent_val x 1#u32 (by decide)
  refine ⟨z,?_,hcz,?_⟩
  · change ProverRwSuccessInverseInstall.Src.mInv x=_
    unfold ProverRwSuccessInverseInstall.Src.mInv
      ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
    simp only [ProverRwSuccessInverseSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ProverRwDictionaryDerived.mEq,
      ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ProverRwSuccessInverseSource.field.M31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO,
      nonzero,decide_false,Bool.false_eq_true,bind_tc_ok,if_false,lift,ProverRwSuccessInverseSource.field.M31.pow,
      ProverRwSuccessInverseSource.field.M31.ONE,AspisR1ProducerRelease47.field.M31.ONE]
    unfold ProverRwSuccessPowerTotal.S.pow at hz
    change ProverRwSuccessInverseSource.field.M31.pow_loop exponent x 1#u32=.ok z at hz
    unfold exponent at hz
    rw [hz]
    rfl
  · have one : decode 1#u32=1 := rfl
    rw [one,one_mul] at hvz
    rw [←ProverCommitInverse48.chain_exponent,ProverCommitInverse48.inverse_decode] at hvz
    exact hvz

theorem canonical_injective (a b : U32) (ha : canonical a) (hb : canonical b)
    (same : decode a=decode b) : a=b := by
  have val := congrArg ZMod.val same
  change a.val % AspisCircleGroupOrder.P=b.val % AspisCircleGroupOrder.P at val
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at val
  exact UScalar.eq_of_val_eq val

theorem fixed_chain (ops : ExternalFuns) (x : U32) (nonzero : x≠0#u32) :
    (ProverRwSuccessInverseInstall.selected ops).op105 x=
      .ok (some (ProverCommitInverse48.inverseWord x)) := by
  obtain ⟨z,hz,hcz,hvz⟩ := exact_result ops x nonzero
  have same : z=ProverCommitInverse48.inverseWord x := canonical_injective z _ hcz
    (ProverCommitInverse48.inverse_canonical x)
    (hvz.trans (ProverCommitInverse48.inverse_decode x).symm)
  rw [same] at hz
  exact hz
#print axioms exponent_val
#print axioms exact_result
#print axioms canonical_injective
#print axioms fixed_chain
end R1Z.ProverRwSuccessScalarInverseExact
