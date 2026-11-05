import NIY_FinalCut
import NIY_C_FinalCut
set_option autoImplicit false
noncomputable section
namespace NIY_FinalPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport AspisR1
open NID_ResumeEmission

/-- Exact final Prepared/Accumulator mapping at the same returned weights/offset.
No success or independently chosen output is a premise. -/
theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (weights : alloc.vec.Vec aspis_core.field.QM31) (at2 : Usize) (r50 : verifier.Reader) :
 NIL_StatePort.reply (NIY_FinalCut.finish reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 weights at2 r50)=
 NIY_C_FinalCut.finish (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (NIL_Carriers.e val) (NIL_Carriers.e val1) (NIL_Carriers.e val2) (NIL_Carriers.e val3) (NIL_Carriers.k val4) queries (NIL_Carriers.array NIL_Carriers.k semantic_alpha) (NIL_Carriers.k val6) (NIL_Carriers.k val7) (NIL_Carriers.k val8) (NIL_Carriers.k val9) (NIL_Carriers.e val10) (NIL_Carriers.e val11) (NIL_Carriers.k val12) (NIL_Carriers.vec NIL_Carriers.k weights) at2 (NIL_Carriers.reader r50) := by
 unfold NIY_FinalCut.finish NIY_C_FinalCut.finish NIL_StatePort.reply
 with_unfolding_all rw [NIL_ResultCases.outer_ite]
 apply NIL_ResultCases.branch_congr
 · rfl
 · with_unfolding_all rw [outer_bind]
   apply NIL_ResultCases.bind_congr
   intro next
   rfl
#print axioms source
end NIY_FinalPort
