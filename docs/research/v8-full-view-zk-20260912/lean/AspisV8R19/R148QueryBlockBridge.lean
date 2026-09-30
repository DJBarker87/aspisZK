import AspisV8R19.R145QueryInnerBridge
import AspisV8R19.R147QuerySqueezeBridge
import AspisV8R19.QueryBlockStep

set_option autoImplicit false
namespace AspisV8R19.R148QueryBlockBridge

open Aeneas Aeneas.Std Result ControlFlow AspisR86Query
open AspisV8R19.QueryChunkExecution AspisV8R19.QueryChunkModel
open AspisV8R19.QueryBlockWords AspisV8R19.QueryChunkSource
open AspisV8R19.QueryBlockStep AspisV8R19.R145QueryInnerBridge
open AspisV8R19.R147QuerySqueezeBridge
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SamplerWords AspisV8R19.Q22WordScan

abbrev Values := AspisV8R19.QueryChunkExecution.Values
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes

def queryTranscript (H : Bytes → State) (s : State) :
    AspisR137Q22.transcript.Transcript :=
  AspisV8R19.R147QuerySqueezeBridge.toR137
    (AspisV8R19.QueryBlockStep.queryTranscript H s)

theorem source_step (H : Bytes → State) (s : State) :
    AspisR137Q22.transcript.Transcript.squeeze_block (queryTranscript H s) =
      .ok (encodeState (step H s).1,queryTranscript H (step H s).2) := by
  unfold queryTranscript
  rw [AspisV8R19.R147QuerySqueezeBridge.squeeze_map,
    AspisV8R19.QueryBlockStep.source_step]
  rfl

theorem outer_step (H : Bytes → State) (s : State) (out : Values) (draws : Usize)
    (hc : out.val.length ≤ 22) (hd : draws.val < 64) :
    ∃ out1 draws1,
      AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0.body
        22#usize 64#usize 262143#u32 (queryTranscript H s) out draws =
        .ok (if (AspisV8R19.Q22WordScan.scan (view out draws)
          (AspisV8R19.SamplerWords.words 18 (step H s).1)).2
          then .done (queryTranscript H (step H s).2,out1)
          else .cont (queryTranscript H (step H s).2,out1,draws1)) ∧
      view out1 draws1 = (AspisV8R19.Q22WordScan.scan (view out draws)
        (AspisV8R19.SamplerWords.words 18 (step H s).1)).1 ∧
      out1.val.length ≤ 22 ∧ draws1.val ≤ 64 := by
  obtain ⟨out1,draws1,he,hv,hc1,hd1⟩ :=
    AspisV8R19.QueryChunkSource.source_scan_bounded 262143#u32
      (blockWords (step H s).1) emptySlice out draws hc (by omega)
  have hrun := he
  rw [AspisV8R19.QueryChunkExecution.source_loop] at hrun
  simp only [candidates_exact] at hrun hv
  refine ⟨out1,draws1,?_,hv,hc1,hd1⟩
  have hd' : draws < 64#usize := hd
  simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0.body,
    if_pos hd', source_step, bind_tc_ok, lift, chunks_success]
  have hinner := AspisV8R19.R145QueryInnerBridge.inner_exact 262143#u32
    (blockWords (step H s).1) emptySlice out draws (by omega)
  rw [hinner, hrun]
  cases hs : (AspisV8R19.Q22WordScan.scan (view out draws)
    (AspisV8R19.SamplerWords.words 18 (step H s).1)).2 <;> rfl

theorem exhausted_step (self : AspisR137Q22.transcript.Transcript)
    (out : Values) (draws : Usize) (hd : 64 ≤ draws.val) :
    AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0.body
      22#usize 64#usize 262143#u32 self out draws = .ok (.done (self,out)) := by
  have hd' : ¬ draws < 64#usize := by change ¬ draws.val < 64; omega
  simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0.body,
    if_neg hd']

#print axioms source_step
#print axioms outer_step
#print axioms exhausted_step

end AspisV8R19.R148QueryBlockBridge
