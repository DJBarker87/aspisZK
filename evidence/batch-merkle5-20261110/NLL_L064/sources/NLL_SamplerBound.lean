import NHK_NativeBlocks
import NHB_OuterState
set_option autoImplicit false
noncomputable section
namespace NLL_SamplerBound
open Aeneas Aeneas.Std Result AspisR1 AspisR1Query31Transcript
open NGQ_SamplerDriver

def Bounds : Out → Prop
 | .Err _ => True
 | .Ok (qs,_) => ∀ w∈qs.val,w.val<262144

/-- The finish call returns the actual accepted array; it cannot choose a new
array at the source boundary. The bound is the entered advance-array domain. -/
theorem finish (advances : Blocks) (index : Usize) (s : State) (hi : index.val<8)
 (out : Out) (run : finishAdvance advances index s=ok out) (canonical : NHB_Canonical.State s) : Bounds out := by
 rw [←NHB_OuterState.finish_at advances index s hi] at run
 cases out with
 | Err e => exact True.intro
 | Ok pair =>
   rcases pair with ⟨qs,state⟩
   unfold NHB_OuterState.finishCurrent aspis_core.r0_transcript.QueryScan.finish at run
   by_cases full : s.accepted_len=22#usize
   · simp only [aspis_core.r0_transcript.QUERY_COUNT,full,if_true,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at run
     have same:=congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj run))
     rw [←same]
     exact canonical
   · simp only [aspis_core.r0_transcript.QUERY_COUNT,full,if_false,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame] at run
     cases run

/-- Canonicality is transported by the already CLOSED native word/block cuts;
no sampler body or whole-buffer computation is replayed. -/
theorem native {advances : Blocks} {inputs : List (Bytes32×Usize)} {s : State} {out : Out}
 (cuts : NHK_NativeBlocks.Cuts advances inputs s out)
 (indices : ∀ input∈inputs,input.2.val<8) (canonical : NHB_Canonical.State s) : Bounds out := by
 induction cuts with
 | exhausted s out run => exact finish advances 7#usize s (by scalar_tac) out run canonical
 | stopped block index tail s next out words last pending decode edges stop run =>
   have good:=NHB_Canonical.word_invariant (NHK_NativeWords.association edges) canonical (NHB_Canonical.decoded block words decode)
   exact finish advances index next (indices _ (by simp)) out run good
 | continuing block index tail s next out words last pending decode edges stop rest ih =>
   have good:=NHB_Canonical.word_invariant (NHK_NativeWords.association edges) canonical (NHB_Canonical.decoded block words decode)
   exact ih (fun p hp=>indices p (List.mem_cons_of_mem _ hp)) good

set_option pp.proofs false
#print native
#print axioms finish
#print axioms native
end NLL_SamplerBound
end
