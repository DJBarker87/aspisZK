import NLT_NativeWindows
set_option autoImplicit false
noncomputable section
namespace NLT_CodecQuestions
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
theorem resume (ck proof pub : Slice U8) (old fresh : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.resume ck proof pub).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.resume ck proof pub).encode fresh) := rfl
#print axioms resume
theorem powers (gamma : aspis_core.field.wide_exact.WideExact) (old fresh : Result (Array aspis_core.field.wide_exact.WideExact 29#usize)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.powers gamma).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.powers gamma).encode fresh) := rfl
#print axioms powers
theorem inactive (bytes : Slice U8) (old fresh : Result (Option aspis_core.field.wide_exact.WideExact)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.inactive bytes).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.inactive bytes).encode fresh) := rfl
#print axioms inactive
theorem merkle (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (old fresh : Result (core.result.Result Unit verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.merkle proof p folded).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.merkle proof p folded).encode fresh) := rfl
#print axioms merkle
theorem geometry (queries : Array U32 22#usize) (next : Usize) (old fresh : Result (core.result.Result verifier.QueryGeometry verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.geometry queries next).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.geometry queries next).encode fresh) := rfl
#print axioms geometry
theorem pending (weights : Slice aspis_core.field.QM31) (old fresh : Result (core.result.Result verifier.BatchedWeights verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.pending weights).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.pending weights).encode fresh) := rfl
#print axioms pending
theorem query (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (old fresh : Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.query proof p a g geo pending).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.query proof p a g geo pending).encode fresh) := rfl
#print axioms query
theorem flush (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31) (old fresh : Result (Slice aspis_core.field.QM31)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.flush pending weights).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.flush pending weights).encode fresh) := rfl
#print axioms flush
theorem finish (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) (old fresh : Result (core.result.Result Unit verifier.Error)) :
 NLT_NativeWindows.question ((NKE_CommonCodec.finish v p a).encode old)=
 NLT_NativeWindows.question ((NKE_CommonCodec.finish v p a).encode fresh) := rfl
#print axioms finish
end NLT_CodecQuestions
