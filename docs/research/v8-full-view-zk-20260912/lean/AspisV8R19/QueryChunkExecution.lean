import AspisR86Query.Loops
import AspisV8R19.SamplerWordRead

/-! Exact execution of the extracted q22 inner loop on four-byte chunks.
The power-of-two argument guard is deliberately outside this source slice.
No opaque guard/ctpop template is admitted, and no oracle law is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.QueryChunkExecution
open Aeneas Aeneas.Std Result ControlFlow AspisR86Query

abbrev Word := Array U8 4#usize
abbrev Values := alloc.vec.Vec U32
abbrev Output := Values × Usize × U32

def chunks (ws : List Word) (rest : Slice U8) : core.slice.iter.ChunksExact U8 :=
  ⟨ws.map Array.to_slice,rest⟩

theorem contains_exact (v : Values) (x : U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 (alloc.vec.Vec.deref v) x =
      .ok (decide (x ∈ v.val)) := by
  change List.anyM (fun y : U32 => (Result.ok (decide (x = y)))) v.val = _
  generalize v.val = xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.anyM_cons,bind_tc_ok]
      by_cases h : x=y <;> simp [h,ih]
      rfl

def runWords (mask : U32) : List Word → Values → Usize → Result Output
  | [],out,draws => .ok (out,draws,1#u32)
  | word::ws,out,draws =>
      if alloc.vec.Vec.len out = 22#usize then .ok (out,draws,0#u32)
      else if draws = 64#usize then .ok (out,draws,0#u32)
      else do
        let draws1 ← draws + 1#usize
        let candidate := core.num.U32.from_le_bytes word &&& mask
        if candidate ∈ out.val then runWords mask ws out draws1
        else
          let out1 ← alloc.vec.Vec.push out candidate
          runWords mask ws out1 draws1

theorem body_word (mask : U32) (word : Word) (ws : List Word)
    (rest : Slice U8) (out : Values) (draws : Usize) :
    transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
      22#usize 64#usize mask (chunks (word::ws) rest) out draws =
      (if alloc.vec.Vec.len out = 22#usize then .ok (.done (out,draws,0#u32))
      else if draws = 64#usize then .ok (.done (out,draws,0#u32))
      else do
        let draws1 ← draws + 1#usize
        let candidate := core.num.U32.from_le_bytes word &&& mask
        if candidate ∈ out.val then .ok (.cont (chunks ws rest,out,draws1))
        else
          let out1 ← alloc.vec.Vec.push out candidate
          .ok (.cont (chunks ws rest,out1,draws1))) := by
  simp only [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body,
    chunks,List.map_cons,core.slice.iter.IteratorChunksExact.next,bind_tc_ok,
    SamplerWordRead.conversion_success,SamplerWordRead.unwrap_success,lift,contains_exact,
    decide_eq_true_eq]

theorem source_loop (mask : U32) (ws : List Word) (rest : Slice U8)
    (out : Values) (draws : Usize) :
    transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
      (chunks ws rest) 22#usize 64#usize mask out draws = runWords mask ws out draws := by
  induction ws generalizing out draws with
  | nil =>
      rw [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0,loop.eq_def]
      simp only [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body,
        chunks,List.map_nil,core.slice.iter.IteratorChunksExact.next,bind_tc_ok,runWords]
  | cons word ws ih =>
      rw [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0,loop.eq_def]
      simp only [body_word,runWords]
      by_cases hc : alloc.vec.Vec.len out = 22#usize
      · simp [hc]
      · by_cases hd : draws = 64#usize
        · simp [hc,hd]
        · simp only [if_neg hc,if_neg hd]
          cases hnext : draws + 1#usize with
          | fail e => simp
          | div => simp
          | ok next =>
              simp only [bind_tc_ok]
              by_cases hm : core.num.U32.from_le_bytes word &&& mask ∈ out.val
              · simp only [if_pos hm]
                simpa only [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0] using ih out next
              · simp only [if_neg hm]
                cases hp : alloc.vec.Vec.push out (core.num.U32.from_le_bytes word &&& mask) with
                | fail e => simp
                | div => simp
                | ok out1 =>
                    simp only [bind_tc_ok]
                    simpa only [transcript.Transcript.challenge_queries_without_replacement_loop0_loop0] using ih out1 next

theorem empty_does_not_detect_completion (mask : U32) (out : Values) (draws : Usize) :
    runWords mask [] out draws = .ok (out,draws,1#u32) := rfl

theorem completed_stops_before_word (mask : U32) (word : Word) (ws : List Word)
    (out : Values) (draws : Usize) (h : alloc.vec.Vec.len out=22#usize) :
    runWords mask (word::ws) out draws = .ok (out,draws,0#u32) := by simp [runWords,h]

theorem exhausted_stops_before_word (mask : U32) (word : Word) (ws : List Word)
    (out : Values) :
    runWords mask (word::ws) out 64#usize = .ok (out,64#usize,0#u32) := by
  simp [runWords]

#print axioms contains_exact
#print axioms body_word
#print axioms source_loop
#print axioms empty_does_not_detect_completion
#print axioms completed_stops_before_word
#print axioms exhausted_stops_before_word
end AspisV8R19.QueryChunkExecution
