import R1Z.PV_RDCD4_CopyWindow194
import R1Z.PV_RDCD4_SliceRange194
import R1Z.PV_DL_UpdatePlan
set_option autoImplicit false
namespace R1Z.PV_RDCD5_BufferSource
open Aeneas Aeneas.Std Result

/-- Byte-level source view of set_pos_unchecked. Its original invariant makes
u8 truncation the identity. No semantics is assigned to invalid get_pos UB. -/
def storedCursor (n : Nat) : Nat := n % 256

theorem cursor_transport (n : Nat) (h : n < 64) : storedCursor n = n := by
  exact Nat.mod_eq_of_lt (by omega)

/-- Concrete Eager suffix: one bulk call iff nonempty, then a prefix copy and
cursor write. The callback is the original Result-valued compression boundary. -/
def finish {S : Type} (compress : S → List U8 → Result S)
    (state : S) (buffer input : List U8) : Result (S × List U8 × Nat) := do
  let split := PV_DL_BatchPlan.bulk input
  let state ← if split.1 = [] then ok state else compress state split.1
  let buffer ← PV_RDCD4_CopyWindow194.source buffer 0 split.2
  ok (state,buffer,storedCursor split.2.length)

def finishReference {S : Type} (compress : S → List U8 → Result S)
    (state : S) (buffer input : List U8) : Result (S × List U8 × Nat) := do
  let split := PV_DL_BatchPlan.bulk input
  let state ← PV_DL_BatchPlan.run compress state input
  ok (state,PV_DL_UpdatePlan.write buffer 0 split.2,split.2.length)

theorem finish_binding {S : Type} (compress : S → List U8 → Result S)
    (state : S) (buffer input : List U8) (hb : buffer.length = 64) :
    finish compress state buffer input = finishReference compress state buffer input := by
  have ht := PV_DL_BatchPlan.remainder input
  have hc := PV_RDCD4_CopyWindow194.binding buffer 0
    (PV_DL_BatchPlan.bulk input).2 (by omega)
  have hp := cursor_transport (PV_DL_BatchPlan.bulk input).2.length ht
  have hr : (if (PV_DL_BatchPlan.bulk input).1 = [] then ok state
      else compress state (PV_DL_BatchPlan.bulk input).1) =
      PV_DL_BatchPlan.run compress state input := by
    by_cases he : (PV_DL_BatchPlan.bulk input).1 = []
    · rw [if_pos he,PV_DL_BatchPlan.no_bulk compress state input he]
    · rw [if_neg he,PV_DL_BatchPlan.single_bulk compress state input he]
  simp only [finish,finishReference,hc,bind_tc_ok,hp,hr]
  rfl

/-- Every source branch is retained: short input, nonzero initial cursor,
checked split_at, first-block copy and call, bulk call, suffix copy and cursor.
The body is defined only as a source model; structural binding is separate. -/
def source {S : Type} (compress : S → List U8 → Result S)
    (state : S) (buffer : List U8) (pos : Nat) (input : List U8) :
    Result (S × List U8 × Nat) :=
  if input.length < 64-pos then do
    let out ← PV_RDCD4_CopyWindow194.source buffer pos input
    ok (state,out,storedCursor (pos+input.length))
  else if pos=0 then finish compress state buffer input
  else do
    let left ← PV_RDCD4_SliceRange194.index input 0 (64-pos)
    let right ← PV_RDCD4_SliceRange194.index input (64-pos) input.length
    let out ← PV_RDCD4_CopyWindow194.source buffer pos left
    let state ← compress state out
    finish compress state out right

/-- Existing V236 model link, with its original safe Eager64 domain. No
callback equality, totality, singleton-fold law, or source premise is added. -/
theorem source_instance {S : Type} (compress : S → List U8 → Result S)
    (state : S) (buffer : List U8) (pos : Nat) (input : List U8)
    (hb : buffer.length = 64) (hp : pos < 64) :
    source compress state buffer pos input =
      PV_DL_UpdatePlan.model compress state buffer pos input := by
  by_cases hn : input.length < 64-pos
  · rw [source,if_pos hn,PV_RDCD4_CopyWindow194.binding buffer pos input (by omega),
      bind_tc_ok,cursor_transport (pos+input.length) (by omega)]
    simp only [PV_DL_UpdatePlan.model,PV_DL_UpdatePlan.value,if_pos hn,
      PV_DL_CompressionTrace.run,bind_tc_ok]
    rfl
  · rw [source,if_neg hn]
    by_cases hz : pos=0
    · subst pos
      rw [if_pos rfl,finish_binding compress state buffer input hb]
      simp only [finishReference,PV_DL_UpdatePlan.model,PV_DL_UpdatePlan.value,
        if_neg hn,PV_DL_UpdatePlan.first,PV_DL_UpdatePlan.start,if_true,
        List.drop_zero,List.nil_append,PV_DL_BatchPlan.run]
    · rw [if_neg hz]
      have hrem : 64-pos ≤ input.length := by omega
      have hl : (PV_RDCD4_SliceRange194.window input 0 (64-pos)).length = 64-pos := by
        simpa using PV_RDCD4_SliceRange194.length input 0 (64-pos) hrem
      rw [PV_RDCD4_SliceRange194.success input 0 (64-pos) (by omega) hrem,bind_tc_ok,
        PV_RDCD4_SliceRange194.success input (64-pos) input.length hrem (by omega),bind_tc_ok,
        PV_RDCD4_CopyWindow194.binding buffer pos _ (by omega),bind_tc_ok]
      have hw : PV_RDCD4_SliceRange194.window input 0 (64-pos) = input.take (64-pos) := by
        simp only [PV_RDCD4_SliceRange194.window,List.drop_zero,Nat.sub_zero]
      have hr : PV_RDCD4_SliceRange194.window input (64-pos) input.length = input.drop (64-pos) := by
        unfold PV_RDCD4_SliceRange194.window
        rw [← List.length_drop]
        exact List.take_length
      rw [hw,hr]
      have hf := PV_DL_UpdatePlan.first_length buffer input pos hb hp hrem
      have he : PV_RDCD4_CopyWindow194.splice buffer pos (input.take (64-pos)) =
          PV_DL_UpdatePlan.first buffer pos input := by
        rw [PV_DL_UpdatePlan.first,if_neg hz]
        rfl
      rw [he]
      simp only [finish_binding compress _ _ _ hf]
      simp only [PV_DL_UpdatePlan.model,PV_DL_UpdatePlan.value,if_neg hn,
        PV_DL_UpdatePlan.start,if_neg hz,PV_DL_CompressionTrace.run,
        List.singleton_append,PV_DL_CompressionTrace.run,bind_assoc_eq]
      rfl

#print axioms cursor_transport
#print axioms finish_binding
#print axioms source_instance
end R1Z.PV_RDCD5_BufferSource
