import NBL_QueryQuietFinish
import NBL_MaterialHashReplay
import NBL_QueryTrace
set_option autoImplicit false
namespace AspisR1.NBL_QueryHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

def log {H : Type} {D : aspis_core.Digest32 H}
    {before : transcript.Transcript H} {row : U8} {payload : Slice U8}
    (t : NBL_QueryTrace.Trace D before row payload) : NBL_BlockTrace.Log :=
  (NBA_Transcript.absorbParts before.state t.tag payload,t.absorbed)::NBL_MaterialHashReplay.log t.pairs

/-- ALL seventeen eager query hash attempts, even when decoding rejects or
selects an earlier state; exact full Result on the SAME local carrier trace. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (t : NBL_QueryTrace.Trace D before row payload) :
    run (PreparedQueryEffects.queries effects NBL_QueryDictionary.boundaries D before row payload)=
      (NBL_HashReplay.events D before.hash (log t),NBL_QueryPort.port t.afterAbsorb t.result) := by
  have absorbed := NBL_HashReplay.absorb D before row t.tag payload t.absorbed t.tagCall t.absorbCall
  have material := NBL_MaterialHashReplay.source D before.hash t.absorbed t.pairs
  have decoded := NBL_QueryWalk.decoder t.pairs.blocks t.pairs.advances
    Query31ConcreteDriverTraceFacts.sourceDefaultState t.result t.walk
  change NBL_QueryDictionary.boundaries.decode t.pairs.blocks t.pairs.advances=
    Query31ConcreteMaterializedSchedule.adaptScanResult t.result at decoded
  have finished := NBL_QueryPort.source D t.afterAbsorb t.pairs.blocks t.pairs.advances t.result decoded
  simp only [NBL_QueryTrace.Trace.afterAbsorb] at finished
  rw [NBL_QueryEffectFactor.source]
  unfold NBL_QueryEffectFactor.queries
  simp only [bind_run,absorbed,chain,material,Aeneas.Std.uncurry,
    NBL_QueryQuietFinish.source,finished,NBL_QueryTrace.Trace.afterAbsorb,
    NBL_HashReplay.events,log,List.map_cons,List.cons_append,List.nil_append,List.append_nil]

theorem length {H : Type} {D : aspis_core.Digest32 H}
    {before : transcript.Transcript H} {row : U8} {payload : Slice U8}
    (t : NBL_QueryTrace.Trace D before row payload) : (log t).length=17 := rfl

#print axioms source
#print axioms length
end AspisR1.NBL_QueryHashReplay
