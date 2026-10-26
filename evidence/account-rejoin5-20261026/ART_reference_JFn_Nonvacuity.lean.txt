import JFn_TX2
import JFn_HashModelNonvacuity
import JFn_AccumulationFlush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Local model non-vacuity only: the three authentication equations and
actual reader coexist with all real ordered decoder arrays and returning
native line folds. No claim of SHA256 or accepted2 is made. -/
theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (seed : Port3_NativeQueryBody.Ops) :
    ∃ H : Bytes → State,
      JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
          ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
      ∀ i : Fin 12,
        (JFn_ArrayBuilder.ops seed).op0 4#usize
          (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
            (JFn_ArrayBuilder.ops seed)) (JFo_Opening.value (JFn_Values.position i))=ok (JFn_Values.value i) ∧
        ∀ inverse : Array U32 5#usize, ∃ out,
          SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i) inverse=ok out ∧
          Port4C_QueryArithmetic.CanonE out := by
  exact ⟨JFn_HashModelNonvacuity.extension background,JFn_HashModelNonvacuity.realizes background,
    JFn_HashModelNonvacuity.reader D hash background,
    fun i => ⟨JFn_Values.source seed i,JFn_Lines.source i⟩⟩

/-- Each real line output can feed the actual first remaining accumulation
and mutable flush without any accumulator-success premise. The geometry node
is still a parameter; the query's preceding equality gate remains open. -/
theorem line_accumulation (seed : Port3_NativeQueryBody.Ops) (i : Fin 12)
    (inverse : Array U32 5#usize) (node : U32) :
    ∃ value out after flushed,
      SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i) inverse=ok value ∧
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
        JFo_Prepared.value JFo_Prepared.accumulator node value JFo_Pending.value=ok (out,after) ∧
      out.next=11#usize ∧ Port3_FlushInstall.flush after out.weights.deref=ok flushed ∧
      flushed.val.length=64 := by
  obtain ⟨value,line,canonical⟩:=JFn_Lines.source i inverse
  obtain ⟨out,after,flushed,run,_,next,flush,size,_⟩:=JFn_AccumulationFlush.source seed node value canonical
  exact ⟨value,out,after,flushed,line,run,next,flush,size⟩

#print axioms inhabited
#print axioms line_accumulation
#print inhabited
#print line_accumulation
end AspisR1.JFn_Nonvacuity
end
