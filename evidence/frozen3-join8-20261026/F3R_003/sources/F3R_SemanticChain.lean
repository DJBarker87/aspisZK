import F3R_SemanticStep
import F3K_CodeBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_SemanticChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

def code {Hash : Type} (D : aspis_core.Digest32 Hash) (pre : r1_wire.Prefix) :
    List U8 → r1_wire.SemanticTranscript Hash → Code
      (core.result.Result (List aspis_core.field.QM31 × r1_wire.SemanticTranscript Hash) r1_wire.Error)
  | [],t => pure (.Ok ([],t))
  | row::rows,t => do
      let vr ← r1_wire.Prefix.validated_record pre row
      match vr with
      | .Err e => pure (.Err e)
      | .Ok r =>
        let (value,t') ← S1SemanticCode.semanticValidated D t r
        match value with
        | .Err e => pure (.Err e)
        | .Ok q =>
          let rest ← code D pre rows t'
          match rest with
          | .Err e => pure (.Err e)
          | .Ok (qs,t'') => pure (.Ok (q::qs,t''))

theorem trace {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (t : SourceFull25.Trace D pre before after cs)
    (below : ∀ c∈cs,c.row.val<25) :
    erase (code D pre (cs.map (fun c=>c.row)) before)=ok (.Ok (cs.map (fun c=>c.q),after)) ∧
    observe (run (code D pre (cs.map (fun c=>c.row)) before)).1=sourceLog cs := by
  induction t with
  | nil self => exact ⟨rfl,rfl⟩
  | @cons after cs c tail ih =>
    have cb := below c List.mem_cons_self
    have next := ih (fun d hd=>below d (List.mem_cons_of_mem c hd))
    have ret := F3R_SemanticStep.returned c cb
    simp only [List.map_cons,code,c.validated]
    erw [F3K_CodeStep.pure_step]
    constructor
    · rw [AuS1_Trace.erase_bind,ret]
      simp only [bind_tc_ok]
      rw [AuS1_Trace.erase_bind,next.1]
      rfl
    · erw [F3K_CodeBind.success _ _ _ ret]
      erw [F3K_CodeBind.success _ _ _ next.1]
      simp only [F3J_ValidatedLog.semantic c cb,observe,run,List.flatMap_nil,List.append_nil]
      exact congrArg (callLog c ++ ·) next.2

#print axioms trace
end AspisR1.F3R_SemanticChain
end
