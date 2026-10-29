import R1Z.PV_RunJoin_EncoderBasisSource49
import R1Z.PV_RunJoin_EncoderEvaluation49
import R1Z.PV_DL_EncoderNative
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderValue49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
def run (q : Array S 1024#usize) (x y : S) : Result S := do
  let basis ← ProverCommitNativeEval48.basis x
  ProverCommitNativePair48.evaluate q basis y

theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hzero : inst.ZERO=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO))
    (hone : inst.ONE=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (hs : ∀ a b, inst.sub (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub a b))
    (q : Array S 1024#usize) (x y : S) :
    PV_DL_EncoderNative.value inst (amap f q) ⟨f x,f y⟩=mapResult f (run q x y) := by
  rw [PV_DL_EncoderNative.source_reference]
  unfold PV_CB_OwnedEncoder.owned.encoder run
  rw [PV_DL_EncoderBasis.basis_source,PV_RunJoin_EncoderBasisSource49.complete inst f hone hm ha hs x]
  symm
  apply PV_RunJoin_WeightMap46.map_bind (amap f) f
  intro basis
  exact (PV_RunJoin_EncoderEvaluation49.complete inst f hzero hm ha q basis y).symm
#print axioms run
#print axioms complete
end R1Z.PV_RunJoin_EncoderValue49
