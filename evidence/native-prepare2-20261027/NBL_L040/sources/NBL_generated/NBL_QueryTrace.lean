import NBL_MaterialTrace
import NBL_QueryWalk
import NBL_QueryFinish
set_option autoImplicit false
namespace AspisR1.NBL_QueryTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NBL_QueryDictionary
abbrev Bytes32 := Array U8 32#usize

/-- Local typed digest/word/scan/finish observations of ONE query call. No
complete decoder/query Result equality or independently selected state. -/
structure Trace {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8) where
  tag : U8
  tagCall : (160#u8+row : Result U8)=ok tag
  absorbed : Bytes32
  absorbCall : D.digest before.hash (NBA_Transcript.absorbParts before.state tag payload)=ok absorbed
  pairs : NBL_MaterialTrace.Trace D before.hash absorbed
  result : Result NBA_QueryDriver.Out
  walk : NBL_QueryWalk.Trace pairs.advances 7#usize
    (pairs.blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
    Query31ConcreteDriverTraceFacts.sourceDefaultState result

def afterAbsorb {H : Type} {D : aspis_core.Digest32 H}
    {before : transcript.Transcript H} {row : U8} {payload : Slice U8}
    (t : Trace D before row payload) : transcript.Transcript H := {before with state:=t.absorbed}

def port {H : Type} (before : transcript.Transcript H) : Result NBA_QueryDriver.Out →
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  | .ok (.Ok (queries,state)) => ok (.Ok queries,{before with state:=state})
  | .ok (.Err _) => ok (.Err .Transcript,before)
  | .fail e => .fail e
  | .div => .div

/-- Complete installed query Result, including first rejection and its absorbed
state, from the SAME eager pairs and locally linked native scanner trace. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (t : Trace D before row payload) :
    NBA_Installed.actual.sampling.queries D before row payload=port t.afterAbsorb t.result := by
  rw [NBL_QueryDictionary.installed,NBA_QueryJoin.source,NBL_QueryFinish.factor]
  have absorbed := NBA_Transcript.absorb D before row t.tag payload t.absorbed t.tagCall t.absorbCall
  rw [absorbed,bind_tc_ok,NBL_MaterialTrace.source D before.hash t.absorbed t.pairs,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have decoded := NBL_QueryWalk.decoder t.pairs.blocks t.pairs.advances
    Query31ConcreteDriverTraceFacts.sourceDefaultState t.result t.walk
  change boundaries.decode t.pairs.blocks t.pairs.advances=
    Query31ConcreteMaterializedSchedule.adaptScanResult t.result at decoded
  cases hr : t.result with
  | fail e =>
    rw [hr] at decoded
    simp only [port,hr,NBA_QueryFactor.finishQuery,decoded,
      Query31ConcreteMaterializedSchedule.adaptScanResult,bind_tc_fail]
  | div =>
    rw [hr] at decoded
    simp only [port,hr,NBA_QueryFactor.finishQuery,decoded,
      Query31ConcreteMaterializedSchedule.adaptScanResult,bind_tc_div]
  | ok inner =>
    cases inner with
    | Err e =>
      rw [hr] at decoded
      exact NBL_QueryFinish.error boundaries D t.afterAbsorb t.pairs.blocks t.pairs.advances
        (Query31ConcreteMaterializedSchedule.adaptQueryError e) decoded
    | Ok pair =>
      rcases pair with ⟨q,state⟩
      rw [hr] at decoded
      exact NBL_QueryFinish.success D t.afterAbsorb t.pairs.blocks t.pairs.advances q state decoded

#print axioms source
end AspisR1.NBL_QueryTrace
