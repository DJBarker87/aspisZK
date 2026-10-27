import XRv_DecodedWords
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRv_QueryDriver
abbrev State := List U32 × Nat × Bool × Array U8 32#usize

def step (blocks advances : Array (Array U8 32#usize) 8#usize)
 (s : State) (i : Nat) : Result State := do
 let (accepted,draws,stopped,_) := s
 if stopped then ok s else do
  let block ← Array.index_usize blocks (XRn_Join_usize i)
  let advance ← Array.index_usize advances (XRn_Join_usize i)
  let (accepted,draws,stop) := (XRt_QueryWords.words block).foldl XRn_Join_scanWord (accepted,draws,false)
  ok (accepted,draws,stop,advance)

theorem stopped (blocks advances : Array (Array U8 32#usize) 8#usize)
 (indices : List Nat) (accepted : List U32) (draws : Nat) (selected : Array U8 32#usize) :
 indices.foldlM (step blocks advances) (accepted,draws,true,selected) =
 ok (accepted,draws,true,selected) := by
 induction indices with
 | nil => rfl
 | cons i rest ih =>
   simp only [List.foldlM_cons,step,↓reduceIte,bind_tc_ok]
   exact ih

def drive (blocks advances : Array (Array U8 32#usize) 8#usize) : List Nat → State → Result State
 | [],s => ok s
 | i::rest,s => if s.2.2.1 then ok s else do
   let next ← step blocks advances s i
   drive blocks advances rest next

theorem short_circuit (blocks advances : Array (Array U8 32#usize) 8#usize)
 (indices : List Nat) (s : State) :
 drive blocks advances indices s = indices.foldlM (step blocks advances) s := by
 induction indices generalizing s with
 | nil => rfl
 | cons i rest ih =>
   rcases s with ⟨a,d,stop,state⟩
   cases stop with
   | false => simp only [drive,Bool.false_eq_true,↓reduceIte,List.foldlM_cons]; congr 1; funext next; exact ih next
   | true =>
     rw [stopped]
     rfl

theorem driver (blocks advances : Array (Array U8 32#usize) 8#usize) :
 aspis_core.r0_transcript.queries_from_pairs blocks advances = (do
  let (accepted,_,_,state) ← drive blocks advances (List.range 8)
   ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8))
  dite (accepted.length = 22)
   (fun h => ok (.Ok (⟨accepted,h⟩,state)))
   (fun _ => ok (.Err (.DrawLimitExhausted (XRn_Join_usize accepted.length) 64#usize)))) := by
 rw [short_circuit]
 rfl

#print axioms stopped
#print axioms short_circuit
#print axioms driver
end XRv_QueryDriver
