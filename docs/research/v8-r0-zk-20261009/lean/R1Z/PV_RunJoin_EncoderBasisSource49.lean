import R1Z.PV_RunJoin_EncoderStages49
import R1Z.ProverCommitNativeEval48
import R1Z.PV_RunJoin_WeightArray46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderBasisSource49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hone : inst.ONE=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (hs : ∀ a b, inst.sub (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub a b))
    (x : S) : PV_DL_EncoderBasis.value inst (f x)=
      mapResult (amap f) (ProverCommitNativeEval48.basis x) := by
  unfold PV_DL_EncoderBasis.value ProverCommitNativeEval48.basis
  rw [hone]
  simp only [bind_tc_ok]
  rw [←PV_RunJoin_WeightArray46.replicate]
  exact PV_RunJoin_EncoderStages49.complete inst f hone hm ha hs 9 _ 1#usize x (by decide)
#print axioms complete
end R1Z.PV_RunJoin_EncoderBasisSource49
