import AspisV8R19.R143QueryEntryBridge
import AspisV8R19.QueryChunkExecution

/-! Exact R137 query scan on four-byte words.
The wrapping increment equals checked arithmetic throughout the actual
64-draw bound; vector failures and divergence remain in the equality. -/
set_option autoImplicit false
namespace AspisV8R19.R145QueryInnerBridge

open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.R143QueryEntryBridge
open AspisV8R19.SamplerWordRead
open AspisV8R19.QueryChunkExecution

abbrev Word := AspisV8R19.QueryChunkExecution.Word
abbrev Values := AspisV8R19.QueryChunkExecution.Values

private theorem wrapping_add_value (draws : Usize) (h : draws.val < 64) :
    (Std.Usize.wrapping_add draws 1#usize).val = draws.val + 1 := by
  simp only [Std.Usize.wrapping_add_val_eq, UScalar.size]
  have h1 : (1#usize : Usize).val = 1 := rfl
  rw [h1]
  have hlt : draws.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
    have hbound : draws.val + 1 ≤ UScalar.cMax .Usize := by
      have := Usize.cMax_bound
      scalar_tac
    exact UScalar.bound_suffices .Usize (draws.val + 1) hbound
  exact Nat.mod_eq_of_lt hlt

theorem body_word (mask : U32) (word : Word) (ws : List Word)
    (rest : Slice U8) (out : Values) (draws : Usize)
    (hd : draws.val ≤ 64) :
    AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body
      22#usize 64#usize mask (AspisV8R19.QueryChunkExecution.chunks (word::ws) rest) out draws =
      (if alloc.vec.Vec.len out = 22#usize then .ok (.done (out,draws,0#u32))
      else if draws = 64#usize then .ok (.done (out,draws,0#u32))
      else do
        let draws1 ← draws + 1#usize
        let candidate := core.num.U32.from_le_bytes word &&& mask
        if candidate ∈ out.val then .ok (.cont (AspisV8R19.QueryChunkExecution.chunks ws rest,out,draws1))
        else
          let out1 ← alloc.vec.Vec.push out candidate
          .ok (.cont (AspisV8R19.QueryChunkExecution.chunks ws rest,out1,draws1))) := by
  simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body,
    AspisV8R19.QueryChunkExecution.chunks, List.map_cons,
    core.slice.iter.IteratorChunksExact.next, bind_tc_ok]
  by_cases hc : alloc.vec.Vec.len out = 22#usize
  · simp [hc]
  · by_cases he : draws = 64#usize
    · simp [hc,he]
    · have hdraw : draws.val < 64 := by
        have hne : draws.val ≠ 64 := by
          intro hv
          apply he
          apply UScalar.eq_of_val_eq
          exact hv
        omega
      rw [bounded_draw_increment draws hdraw]
      simp only [bind_tc_ok, AspisV8R19.SamplerWordRead.conversion_success,
        AspisV8R19.SamplerWordRead.unwrap_success, lift, AspisV8R19.QueryChunkExecution.contains_exact,
        decide_eq_true_eq]

theorem inner_exact (mask : U32) (ws : List Word) (rest : Slice U8)
    (out : Values) (draws : Usize) (hd : draws.val ≤ 64) :
    AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
      (AspisV8R19.QueryChunkExecution.chunks ws rest) 22#usize 64#usize mask out draws =
      AspisV8R19.QueryChunkExecution.runWords mask ws out draws := by
  induction ws generalizing out draws with
  | nil =>
      rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0,
        loop.eq_def]
      simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0.body,
        AspisV8R19.QueryChunkExecution.chunks, List.map_nil,
        core.slice.iter.IteratorChunksExact.next, bind_tc_ok,
        AspisV8R19.QueryChunkExecution.runWords]
  | cons word ws ih =>
      rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0,
        loop.eq_def]
      have hbody := body_word mask word ws rest out draws hd
      simp only [hbody, AspisV8R19.QueryChunkExecution.runWords]
      by_cases hc : alloc.vec.Vec.len out = 22#usize
      · simp [hc]
      · by_cases he : draws = 64#usize
        · simp [hc,he]
        · have hdraw : draws.val < 64 := by
            have hne : draws.val ≠ 64 := by
              intro hv
              apply he
              apply UScalar.eq_of_val_eq
              exact hv
            omega
          simp only [if_neg hc, if_neg he]
          rw [bounded_draw_increment draws hdraw]
          simp only [bind_tc_ok]
          have hdnext : (Std.Usize.wrapping_add draws 1#usize).val ≤ 64 := by
            rw [wrapping_add_value draws hdraw]
            omega
          by_cases hm : core.num.U32.from_le_bytes word &&& mask ∈ out.val
          · simp only [if_pos hm]
            simpa only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0] using
              (ih out (Std.Usize.wrapping_add draws 1#usize) hdnext)
          · simp only [if_neg hm]
            cases hp : alloc.vec.Vec.push out (core.num.U32.from_le_bytes word &&& mask) with
            | fail e => simp
            | div => simp
            | ok out1 =>
                simp only [bind_tc_ok]
                simpa only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0] using
                  (ih out1 (Std.Usize.wrapping_add draws 1#usize) hdnext)

#print axioms body_word
#print axioms inner_exact

end AspisV8R19.R145QueryInnerBridge
