import AspisV8R19.R167TranscriptPrimitiveExecution

/-! Actual packed/multipart absorb hash-call boundary with arbitrary failing or
 diverging source hash. No probability law or complete callback trace claim. -/
set_option autoImplicit false
namespace AspisV8R19.R205AbsorbHashCall
open Aeneas Aeneas.Std Result
open R137TranscriptPrimitiveBridge
open AspisR137Transcript

def packed (state : Array U8 32#usize) (label : U8) (data : Slice U8)
    (hd : data.val.length ≤ 158) : Slice U8 :=
  ⟨state.val ++ 0#u8 :: label :: data.val, by
    have hh : 192 ≤ Usize.max := (192#usize : Usize).hSize
    have h32 : (32#usize : Usize).val = 32 := rfl
    simp only [List.length_append, List.length_cons, state.property, h32]
    omega⟩

def packedMessage (state : Array U8 32#usize) (label : U8) (data : Slice U8)
    (hd : data.val.length ≤ 158) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [packed state label data hd])

def multipartMessage (state : Array U8 32#usize) (label : U8) (data : Slice U8) :
    Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,label]),data])

theorem short_execution (t : transcript.Transcript) (label : U8) (data : Slice U8)
    (short : data.len ≤ transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize) :
    transcript.Transcript.absorb t label data = (do
      let next ← t.hash (packedMessage t.state label data (by
        change data.val.length ≤ _ at short
        rwa [packed_payload_limit] at short))
      ok {t with state := next}) := by
  have hs : t.state.val.length = 32 := t.state.property
  have hd : data.val.length ≤ 158 := by
    change data.val.length ≤
      (AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize).val at short
    rwa [packed_payload_limit] at short
  have hend :
      (Std.Usize.wrapping_add 34#usize data.len).val = 34 + data.val.length := by
    rw [Std.Usize.wrapping_add_val_eq, Slice.len_val]
    have h34 : (34#usize : Std.Usize).val = 34 := rfl
    rw [h34]
    change (34 + data.val.length) % UScalar.size .Usize =
      34 + data.val.length
    apply Nat.mod_eq_of_lt
    have hsize : 192 < UScalar.size .Usize := by
      simpa using (192#usize : Std.Usize).hSize
    omega
  have htotal : 34 + data.val.length ≤ 192 := by omega
  have hspan : 34#usize ≤ Std.Usize.wrapping_add 34#usize data.len := by
    change 34 ≤ (Std.Usize.wrapping_add 34#usize data.len).val
    rw [hend]
    omega
  have h192val : (192#usize : Std.Usize).val = 192 := rfl
  have h32val : (32#usize : Std.Usize).val = 32 := rfl
  have h34val : (34#usize : Std.Usize).val = 34 := rfl
  have h33val : (33#usize : Std.Usize).val = 33 := rfl
  have h32192 : 32 ≤ 192 := by omega
  have hfull :
      32 + (data.val.length + 1 + 1) + (158 - data.val.length) = 192 := by
    omega
  unfold transcript.Transcript.absorb
  simp only [lift, bind_tc_ok]
  rw [if_pos short]
  simp only [
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.from_slice, Array.update,
    core.array.Array.index, core.ops.index.IndexSlice,
    core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Array.to_slice, Slice.length, Slice.len]
  simp only [Array.length_eq, Array.repeat_val, List.length_replicate, hs,
    hend, htotal, hspan, h192val, h32val, h34val, if_true,
    bind_tc_ok]
  simp only [h32192, if_true, true_and, bind_tc_ok,
    initial_scratch_prefix, List.length_replicate]
  simp only [setSlice_zero_repeat 0#u8 t.state.val hs,
    List.length_append, hs, List.length_replicate, Array.getElem?_Usize_eq,
    h32val, h33val, scratch_slot32,
    bind_tc_ok, scratch_slot33_after_dom, set_frame_points, dif_pos]
  simp only [scratch_payload_window 0#u8
      AspisR137Transcript.transcript.DOM_ABSORB label t.state.val
      data.val hs hd,
    List.length_replicate, bind_tc_ok,
    set_payload 0#u8 AspisR137Transcript.transcript.DOM_ABSORB label
      t.state.val data.val hs hd,
    List.length_append, List.length_cons, hs, hfull, if_true, dif_pos,
    populated_prefix 0#u8 AspisR137Transcript.transcript.DOM_ABSORB label
      t.state.val data.val hs]
  simp only [packedMessage,packed, transcript.DOM_ABSORB]
  rfl

theorem long_execution (t : transcript.Transcript) (label : U8) (data : Slice U8)
    (long : ¬data.len ≤ transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize) :
    transcript.Transcript.absorb t label data = (do
      let next ← t.hash (multipartMessage t.state label data)
      ok {t with state := next}) := by
  simp only [transcript.Transcript.absorb,lift,bind_tc_ok,if_neg long,
    multipartMessage,transcript.DOM_ABSORB]

#print axioms short_execution
#print axioms long_execution
end AspisV8R19.R205AbsorbHashCall
