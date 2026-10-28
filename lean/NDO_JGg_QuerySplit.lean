import NDO_JGg_QueryTrace
set_option autoImplicit false
namespace AspisR1.JGg_QuerySplit
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
def finish (B : QueriesModel.Boundaries) {Hash : Type} (D : aspis_core.Digest32 Hash) (self1 : transcript.Transcript Hash)
    (blocks advances : Blocks) : Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript Hash) := do
  let r ← B.decode blocks advances
  let r1 ←
    core.result.Result.map_err
      (transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError
      D) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (q, state7) := val
    let u ← Array.index_usize q 0#usize
    let we ← B.embed u
    trace.value 5#u16 0#usize we
    let u1 ← Array.index_usize q 1#usize
    let we1 ← B.embed u1
    trace.value 5#u16 1#usize we1
    let u2 ← Array.index_usize q 2#usize
    let we2 ← B.embed u2
    trace.value 5#u16 2#usize we2
    let u3 ← Array.index_usize q 3#usize
    let we3 ← B.embed u3
    trace.value 5#u16 3#usize we3
    let u4 ← Array.index_usize q 4#usize
    let we4 ← B.embed u4
    trace.value 5#u16 4#usize we4
    let u5 ← Array.index_usize q 5#usize
    let we5 ← B.embed u5
    trace.value 5#u16 5#usize we5
    let u6 ← Array.index_usize q 6#usize
    let we6 ← B.embed u6
    trace.value 5#u16 6#usize we6
    let u7 ← Array.index_usize q 7#usize
    let we7 ← B.embed u7
    trace.value 5#u16 7#usize we7
    let u8 ← Array.index_usize q 8#usize
    let we8 ← B.embed u8
    trace.value 5#u16 8#usize we8
    let u9 ← Array.index_usize q 9#usize
    let we9 ← B.embed u9
    trace.value 5#u16 9#usize we9
    let u10 ← Array.index_usize q 10#usize
    let we10 ← B.embed u10
    trace.value 5#u16 10#usize we10
    let u11 ← Array.index_usize q 11#usize
    let we11 ← B.embed u11
    trace.value 5#u16 11#usize we11
    let u12 ← Array.index_usize q 12#usize
    let we12 ← B.embed u12
    trace.value 5#u16 12#usize we12
    let u13 ← Array.index_usize q 13#usize
    let we13 ← B.embed u13
    trace.value 5#u16 13#usize we13
    let u14 ← Array.index_usize q 14#usize
    let we14 ← B.embed u14
    trace.value 5#u16 14#usize we14
    let u15 ← Array.index_usize q 15#usize
    let we15 ← B.embed u15
    trace.value 5#u16 15#usize we15
    let u16 ← Array.index_usize q 16#usize
    let we16 ← B.embed u16
    trace.value 5#u16 16#usize we16
    let u17 ← Array.index_usize q 17#usize
    let we17 ← B.embed u17
    trace.value 5#u16 17#usize we17
    let u18 ← Array.index_usize q 18#usize
    let we18 ← B.embed u18
    trace.value 5#u16 18#usize we18
    let u19 ← Array.index_usize q 19#usize
    let we19 ← B.embed u19
    trace.value 5#u16 19#usize we19
    let u20 ← Array.index_usize q 20#usize
    let we20 ← B.embed u20
    trace.value 5#u16 20#usize we20
    let u21 ← Array.index_usize q 21#usize
    let we21 ← B.embed u21
    trace.value 5#u16 21#usize we21
    ok (core.result.Result.Ok q, { self1 with state := state7 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U32 22#usize) (core.convert.FromSame verifier.Error)
        residual
    ok (r2, self1)

def QueriesModel.entry (B : QueriesModel.Boundaries)
  {H : Type} (D : aspis_core.Digest32 H)
  (transcript : transcript.Transcript H) (row : Std.U8)
  (payload : Slice Std.U8) :
  Result (core.result.Result (Array Std.U32 22#usize) verifier.Error)
  := do
  let (r, _) ←
    QueriesModel.queries B D transcript row payload
  ok r

def step {Hash A : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (i : Usize) (state : Bytes32) (blocks advances : Blocks)
    (k : Blocks → Blocks → Bytes32 → Result A) : Result A := do
  let read ← D.digest hash (TranscriptStep.readParts state 1#u8)
  let blocks1 ← Array.update blocks i read
  let next ← D.digest hash (TranscriptStep.readParts state 2#u8)
  let advances1 ← Array.update advances i next
  let state1 ← Array.index_usize advances1 i
  k blocks1 advances1 state1

def later {Hash A : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (blocks advances : Blocks) (state : Bytes32) (k : Blocks → Blocks → Result A) : Result A :=
  step D hash 1#usize state blocks advances fun blocks advances state =>
    step D hash 2#usize state blocks advances fun blocks advances state =>
      step D hash 3#usize state blocks advances fun blocks advances state =>
        step D hash 4#usize state blocks advances fun blocks advances state =>
          step D hash 5#usize state blocks advances fun blocks advances state =>
            step D hash 6#usize state blocks advances fun blocks advances state =>
              step D hash 7#usize state blocks advances fun blocks advances state =>
                k blocks advances
def initial {Hash A : Type} (D : aspis_core.Digest32 Hash) (self : transcript.Transcript Hash)
    (row : U8) (payload : Slice U8) (k : transcript.Transcript Hash → Blocks → Blocks → Result A) : Result A := do
  let self1 ← transcript.Transcript.absorb D self row payload
  let zero := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize zero
  let read ← D.digest self1.hash (TranscriptStep.readParts self1.state 1#u8)
  let (_,back) ← Array.index_mut_usize blocks 0#usize
  let next ← D.digest self1.hash (TranscriptStep.readParts self1.state 2#u8)
  let advances := back next
  let state ← Array.index_usize advances 0#usize
  later D self1.hash (back read) advances state (k self1)

end AspisR1.JGg_QuerySplit
