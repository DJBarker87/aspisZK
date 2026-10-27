import RPz7_F3K_QueryWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryScanCall
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem scan (s sf : Query31ModelDriverChain.QueryScan)
    (block : Array U8 32#usize) (stop : Bool)
    (valid : validState s)
    (success : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s block=ok (stop,sf)) :
    AspisV8R19.Q22WordScan.scan (q22StateOf s)
      (AspisV8R19.SamplerWords.words 18 (decodeState block))=(q22StateOf sf,stop) ∧
    validState sf := by
  obtain ⟨ws,decoded,transition,validAfter⟩ := Query31ModelScanCall.modelScanFn_success
    Query31ConcreteWordsDriverChain.actualQueryWords s sf block stop valid success
  rw [F3K_QueryWords.decoded block ws decoded] at transition
  exact ⟨transition,validAfter⟩

theorem finish (s : Query31ModelDriverChain.QueryScan) (out : Array U32 22#usize)
    (success : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s=ok (.Ok out)) :
    AspisV8R19.Q22WordScan.finish (q22StateOf s)=.ok (out.val.map (fun x=>x.val)) := by
  have fields := (AspisR1Query31Transcript.finish_success_iff s out).mp success
  have count : s.accepted_len.val=22 := by
    have h : s.accepted_len=22#usize := by simpa only [AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT] using fields.1
    exact congrArg (fun n : Usize => n.val) h
  have same : s.accepted=out := fields.2.symm
  unfold q22StateOf acceptedPrefix AspisV8R19.Q22WordScan.finish
  rw [count,same]
  have len : out.val.length=22 := out.property
  simp only [List.take_of_length_le (by omega : out.val.length≤22),List.length_map,len,ite_true]

#print axioms scan
#print axioms finish
end AspisR1.F3K_QueryScanCall
end
