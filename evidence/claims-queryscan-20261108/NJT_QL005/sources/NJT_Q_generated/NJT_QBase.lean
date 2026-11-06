import NGQ_SamplerWords
import NHK_Invocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QBase
open Aeneas Aeneas.Std Result
open AspisR1QueryScanUnrolled
abbrev Bytes := Array U8 32#usize
abbrev Words := Array U32 8#usize
abbrev State := NGQ_SamplerTrace.State
abbrev Finish := core.result.Result (Array U32 22#usize)
 AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError

def rank (b : Bytes) : Words :=
 ⟨(List.range 8).map (r0_transcript.blockRankWord b),by simp⟩

theorem rank_source (b : Bytes) : r0_transcript.block_rank b=ok (rank b) := by
 obtain ⟨a,call⟩:=NGQ_SamplerFromFn.source 8#usize
  r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 b (by
   intro state i hi
   exact ⟨_,state,r0_transcript.block_rank_callback_call_mut_success state i (by simpa only [show (8#usize).val=8 by rfl] using hi)⟩)
 have hcall : r0_transcript.block_rank b=ok a:=call
 have values:=r0_transcript.block_rank_success_words_in_order b a hcall
 have eq : a=rank b:=Subtype.ext values
 simpa only [eq] using hcall

def words (b : Bytes) : Words :=
 ⟨(List.range 8).map (fun j=>r0_transcript.queryMaskWord (r0_transcript.blockRankWord b j)),by simp⟩

theorem words_source (b : Bytes) :
 Query31ConcreteWordsDriverChain.actualQueryWords b=ok (words b) := by
 obtain ⟨a,call,values⟩:=NGQ_SamplerWords.source b
 have eq : a=words b:=Subtype.ext values
 simpa only [eq] using call

def finish (s : State) : Finish :=
 if s.accepted_len=22#usize then .Ok s.accepted
 else .Err (.DrawLimitExhausted s.accepted_len 64#usize)

theorem finish_source (s : State) :
 AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s=ok (finish s) := by
 rfl

#print axioms rank_source
#print axioms words_source
#print axioms finish_source
end AspisR1.NJT_QBase
end
