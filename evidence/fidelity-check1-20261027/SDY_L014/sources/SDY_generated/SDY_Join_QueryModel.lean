import SDY_Join_CheckpointModel
open Aeneas Aeneas.Std Result ControlFlow Error
open SDY_Join_Release
/- r0_transcript.rs QueryScan: the stop test is before each word, never after
   the eighth. Retains duplicate rejection and the selected advance block.
   P6/source/log association OPEN. -/
def SDY_Join_scanWord (s : List U32 × Nat × Bool) (word : U32) : List U32 × Nat × Bool :=
  let (accepted,draws,stopped) := s
  if stopped then s
  else if accepted.length = 22 ∨ draws = 64 then (accepted,draws,true)
  else (if word ∈ accepted then accepted else accepted ++ [word], draws+1,false)
def aspis_core.r0_transcript.queries_from_pairs
    (blocks advances : Array (Array U8 32#usize) 8#usize) :
    Result (core.result.Result (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError) := do
  let (accepted,draws,_,state) ← (List.range 8).foldlM
    (fun (s : List U32 × Nat × Bool × Array U8 32#usize) i => do
      let (accepted,draws,stopped,state) := s
      if stopped then ok s else do
        let block ← Array.index_usize blocks (SDY_Join_usize i)
        let advance ← Array.index_usize advances (SDY_Join_usize i)
        let words := (List.range 8).map fun j =>
          UScalar.ofNat ((SDY_Join_word ((block.val.drop (4*j)).take 4)).val % 262144)
            (by change _ ≤ 4294967295; omega)
        let (accepted,draws,stop) := words.foldl SDY_Join_scanWord (accepted,draws,false)
        ok (accepted,draws,stop,advance))
    ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8))
  dite (accepted.length = 22)
    (fun h => ok (.Ok (⟨accepted,h⟩,state)))
    (fun _ => ok (.Err (.DrawLimitExhausted (SDY_Join_usize accepted.length) 64#usize)))
