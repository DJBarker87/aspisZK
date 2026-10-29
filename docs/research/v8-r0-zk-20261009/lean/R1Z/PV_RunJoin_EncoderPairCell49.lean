import R1Z.PV_RunJoin_EncoderPairTransport49
import R1Z.PV_RunJoin_EncoderPairRead49
import R1Z.PV_RunJoin_EncoderCell49
import R1Z.ProverCommitNativePair48
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderPairCell49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
open PV_RunJoin_EncoderPairTransport49 (pairMap)

theorem complete {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (f : S → E)
    (hm : ∀ a b, inst.mul (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b))
    (ha : ∀ a b, inst.add (f a) (f b)=mapResult f (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b))
    (q : Array S 1024#usize) (basis : Array S 512#usize)
    (j : Usize) (hj : j.val<512) (p0 p1 : S) :
    PV_DL_EncoderFold.step inst (amap f q) (amap f basis) j (f p0) (f p1)=
      mapResult (pairMap f) (ProverCommitNativePair48.step q basis j (p0,p1)) := by
  letI : Inhabited S := ⟨p0⟩
  have he := PV_RunJoin_EncoderPairRead49.even q j hj
  have ho := PV_RunJoin_EncoderPairRead49.odd q j hj
  have hb := PV_RunJoin_EncoderPairRead49.basis basis j hj
  simp only [PV_DL_EncoderFold.step,PV_RunJoin_WeightMap46.index,he,ho,hb,
    mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,
    ProverCommitNativePair48.step]
  exact PV_RunJoin_EncoderPairTransport49.complete f
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul
    AspisR1ProducerRelease47.field.wide_exact.WideExact.add inst.mul inst.add hm ha
    _ _ _ p0 p1
#print axioms complete
end R1Z.PV_RunJoin_EncoderPairCell49
