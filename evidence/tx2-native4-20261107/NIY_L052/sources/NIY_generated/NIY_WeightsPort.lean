import NIY_FinalPort
import NIY_SectionBind
set_option autoImplicit false
noncomputable section
namespace NIY_WeightsPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (val13 : alloc.vec.Vec aspis_core.field.QM31) (r50 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AllocationCut.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 val13 r50)=
 NIY_C_AllocationCut.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) queries (array k semantic_alpha) (k val6) (k val7) (k val8) (k val9) (e val10) (e val11) (k val12) (vec k val13) (reader r50) := by
 with_unfolding_all rw [NIY_FinalCut.source,NIY_C_FinalCut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.weights
 apply NIY_SectionBind.sectionReply
 rintro ⟨weights,at2⟩
 have h := NIY_FinalPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 (vec unK weights) at2 r50
 simpa only [NIL_StatePort.reply,vec_roundtrip unK k k_reverse] using h
#print axioms source
end NIY_WeightsPort
