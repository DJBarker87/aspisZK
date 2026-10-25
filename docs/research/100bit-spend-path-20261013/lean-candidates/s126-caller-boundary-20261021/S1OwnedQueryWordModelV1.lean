import S1OwnedQuerySourceBodyV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result
open Query31ExplicitScanBody

/-- Same actual owned word call, same full returned state, and the existing
Q22 transition. No independent child-call or word interpretation is assumed. -/
theorem owned_step_model (s : CurrentScan) (candidate : U32)
    (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64) :
    ∃ (sf : CurrentScan) (stop : Bool),
      owned_step s.accepted s.accepted_len s.draws candidate=ok (pack sf stop) ∧
      AspisV8R19.Q22WordScan.scan (q22StateOf s) [candidate.val]=(q22StateOf sf,stop) ∧
      Query31ExplicitListLoop.validState sf := by
  have valid := Query31ExplicitListLoop.validState_of_bounds s hlen hd
  obtain ⟨sf,pending,called,model⟩ := Query31ExplicitListLoop.scanListLoop_q22 [candidate] s valid
  have transported : owned_step s.accepted s.accepted_len s.draws candidate=
      ok (pack sf (Query31ExplicitListLoop.optionStop pending)) := by
    rw [owned_step_eq_sourceWord s candidate hlen,sourceWord_eq_scanOne,called]
    rfl
  obtain ⟨a,n,d,b,call,hn,hdraw⟩ :=
    AspisS1OwnedQueryBlock.Total.step_total s.accepted s.accepted_len s.draws candidate hlen hd
  have equal : (a,n,d,b)=pack sf (Query31ExplicitListLoop.optionStop pending) :=
    Result.ok.inj (call.symm.trans transported)
  have range : AspisS1OwnedQueryBlock.Total.validOutput
      (pack sf (Query31ExplicitListLoop.optionStop pending)) := by
    rw [← equal]
    exact ⟨hn,hdraw⟩
  refine ⟨sf,Query31ExplicitListLoop.optionStop pending,transported,?_,?_⟩
  · simpa only [List.map_cons,List.map_nil] using model
  · exact Query31ExplicitListLoop.validState_of_bounds sf range.1 range.2

#print axioms owned_step_model
end AspisS1OwnedQueryBlock.Meaning
