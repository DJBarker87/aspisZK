import R1Z.PV_RunJoin_EncoderPairs49
import R1Z.PV_RunJoin_EncoderFinalTransport49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderEvaluation49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)

theorem uncurry {A B : Type} (k : A → A → B) :
    (fun p : A×A => Aeneas.Std.uncurry k p)=(fun p => k p.1 p.2) := by
  funext p;rcases p with ⟨a,b⟩;rfl

theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hzero : inst.ZERO=ok (f AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO))
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (q : Array S 1024#usize) (basis : Array S 512#usize) (y : S) :
    (do let z ← inst.ZERO
        let (p0,p1) ← PV_CB_OwnedEncoder.owned.encoder_fold inst (amap f q) (amap f basis) 0#usize z z
        let product ← inst.mul (f y) p1
        inst.add p0 product)=
      mapResult f (ProverCommitNativePair48.evaluate q basis y) := by
  rw [hzero]
  simp only [bind_tc_ok]
  rw [PV_DL_EncoderFold.source inst _ _ 512 0#usize _ _ (by decide)]
  rw [PV_RunJoin_EncoderPairs49.complete inst f hm ha q basis 512 0#usize (by decide)]
  simp only [uncurry]
  exact PV_RunJoin_EncoderFinalTransport49.complete f
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul
    AspisR1ProducerRelease47.field.wide_exact.WideExact.add inst.mul inst.add hm ha _ y
#print axioms uncurry
#print axioms complete
end R1Z.PV_RunJoin_EncoderEvaluation49
