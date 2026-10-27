import RPt_FJf_FromLimbsPacked
import RPt_FIp_FastFinishCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_EbyKFinish
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open JFs_TX2_RawMap (pack)

theorem value (self : FIo_Native.fast_pairing.EbyKDot) (out : NE)
    (run : FIo_Native.fast_pairing.EbyKDot.finish self=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=FJf_EbyKCodec.model self := by
  refine ⟨FIp_FastFinishCanonical.finish self out run,?_⟩
  unfold FIo_Native.fast_pairing.EbyKDot.finish at run
  obtain ⟨q0,hq0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,b,c,d,eq0⟩ := JFs_TX2_RawMap.shape q0
  subst q0
  have r0 : Array.index_usize (pack a b c d) 0#usize=ok a := rfl
  have r1 : Array.index_usize (pack a b c d) 1#usize=ok b := rfl
  have r2 : Array.index_usize (pack a b c d) 2#usize=ok c := rfl
  have r3 : Array.index_usize (pack a b c d) 3#usize=ok d := rfl
  simp only [FIo_Native.fast_pairing.canonical.Q.limbs,r0,r1,r2,r3,bind_tc_ok] at run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨e,f,g,h,eq1⟩ := JFs_TX2_RawMap.shape q1
  subst q1
  have r4 : Array.index_usize (pack e f g h) 0#usize=ok e := rfl
  have r5 : Array.index_usize (pack e f g h) 1#usize=ok f := rfl
  have r6 : Array.index_usize (pack e f g h) 2#usize=ok g := rfl
  have r7 : Array.index_usize (pack e f g h) 3#usize=ok h := rfl
  simp only [FIo_Native.fast_pairing.canonical.Q.limbs,r4,r5,r6,r7,bind_tc_ok] at run
  obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => simp only [core.option.Option.unwrap] at run;cases run
  | some z =>
    simp only [core.option.Option.unwrap] at run
    have eq := Result.ok.inj run
    subst out
    have layout := FJf_FromLimbsPacked.value a b c d e f g h z ho
    subst z
    have v0 := FJf_DotMeaning.finish self.c0 (pack a b c d) hq0
    have v1 := FJf_DotMeaning.finish self.c1 (pack e f g h) hq1
    apply QuadraticAlgebra.ext
    · change FJf_RawDecode.q (pack a b c d)=FJf_RawDecode.dot self.c0
      exact v0.2
    · change FJf_RawDecode.q (pack e f g h)=FJf_RawDecode.dot self.c1
      exact v1.2
#print axioms value
end AspisR1.FJf_EbyKFinish
end
