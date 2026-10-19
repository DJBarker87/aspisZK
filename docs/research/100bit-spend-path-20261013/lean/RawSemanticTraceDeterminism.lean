import ExtractedSourceFull25Frames

/-! The source record lookup and semantic call are deterministic. Any two
successful logs over one row schedule and starting transcript therefore retain
one challenge list and ending transcript, even when their witnesses differ. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticTraceDeterminism
open Aeneas Aeneas.Std Result

 theorem semantic_run_unique {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) {rows : List U8}
    {before after after' : r1_wire.SemanticTranscript H}
    {qs qs' : List aspis_core.field.QM31}
    (run : BeginCalls.SemanticRun D pre rows before after qs)
    (other : BeginCalls.SemanticRun D pre rows before after' qs') :
    after = after' ∧ qs = qs' := by
  induction run generalizing after' qs' with
  | nil self => cases other; exact ⟨rfl, rfl⟩
  | @cons row rows self mid after q qs record hr hs tail ih =>
    cases other with
    | @cons _ _ _ mid' _ q' qs' record' hr' hs' tail' =>
      have hrecord : record = record' :=
        core.result.Result.Ok.inj (Result.ok.inj (hr.symm.trans hr'))
      subst record'
      have hp := Result.ok.inj (hs.symm.trans hs')
      have hq : q = q' := core.result.Result.Ok.inj (congrArg Prod.fst hp)
      have hm : mid = mid' := congrArg Prod.snd hp
      subst mid'
      obtain ⟨ha, hqs⟩ := ih tail'
      exact ⟨ha, by rw [hq, hqs]⟩

 theorem source_trace_semantic_run {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) {before after : r1_wire.SemanticTranscript H}
    {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs) :
    BeginCalls.SemanticRun D pre (cs.map SourceFull25.Call.row)
      before after (cs.map SourceFull25.Call.q) := by
  induction run with
  | nil self => exact .nil _
  | cons c tail ih => exact .cons c.validated c.semantic ih

 theorem source_trace_outputs_unique {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) {before after after' : r1_wire.SemanticTranscript H}
    {cs ds : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (other : SourceFull25.Trace D pre before after' ds)
    (hrows : cs.map SourceFull25.Call.row = ds.map SourceFull25.Call.row) :
    after = after' ∧ cs.map SourceFull25.Call.q = ds.map SourceFull25.Call.q := by
  have hrun := source_trace_semantic_run D pre run
  have hother := source_trace_semantic_run D pre other
  rw [← hrows] at hother
  exact semantic_run_unique D pre hrun hother

#print axioms semantic_run_unique
#print axioms source_trace_semantic_run
#print axioms source_trace_outputs_unique
end AspisR1PublicPreparation.RawSemanticTraceDeterminism
