import AspisR137Transcript.Funs
import AspisV8R19.SqueezeOracleBridge

/-! Exact representation and long-absorb bridge for the separately extracted
R137 transcript primitives.  The hash remains an arbitrary total byte oracle;
no randomness, freshness, privacy, or soundness claim is made here. -/
set_option autoImplicit false
namespace AspisV8R19.R137TranscriptPrimitiveBridge

open Aeneas Aeneas.Std Result
open DuplexFrames SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def transcriptFor (H : Bytes → State) (s : State) :
    AspisR137Transcript.transcript.Transcript :=
  ⟨encodeState s, hashAdapter H⟩

def decodedSlice (data : Slice U8) : Bytes := data.val.map decodeByte

def zeroState : State := fun _ => ⟨0, by omega⟩

/- These three lemmas keep the packed absorb proof symbolic.  In particular,
they avoid reducing the source's 192-byte scratch array cell by cell. -/
theorem setSlice_zero_repeat {A : Type} (z : A) (state : List A)
    (hs : state.length = 32) :
    List.setSlice! (List.replicate 192 z) 0 state =
      state ++ List.replicate 160 z := by
  unfold List.setSlice!
  simp only [List.take_zero, List.length_replicate, Nat.zero_add, Nat.sub_zero,
    hs]
  rw [min_eq_left (by omega), List.take_of_length_le (by omega),
    List.drop_replicate]
  norm_num

theorem initial_scratch_prefix {A : Type} (z : A) :
    List.slice 0 32 (List.replicate 192 z) = List.replicate 32 z := by
  simp only [List.slice, List.drop_zero, List.take_replicate]
  norm_num

theorem set_frame_points {A : Type} (z dom label : A) (state : List A)
    (hs : state.length = 32) :
    ((state ++ List.replicate 160 z).set 32 dom).set 33 label =
      state ++ dom :: label :: List.replicate 158 z := by
  rw [List.set_append]
  simp only [hs, Nat.reduceLT, if_false, Nat.reduceSub]
  rw [List.set_append]
  simp only [hs, Nat.reduceLT, if_false, Nat.reduceSub]
  rfl

theorem scratch_slot32 {A : Type} (z : A) (state : List A)
    (hs : state.length = 32) :
    (state ++ List.replicate 160 z)[32]? = some z := by
  rw [List.getElem?_append, hs]
  norm_num

theorem scratch_slot33_after_dom {A : Type} (z dom : A) (state : List A)
    (hs : state.length = 32) :
    ((state ++ List.replicate 160 z).set 32 dom)[33]? = some z := by
  rw [List.set_append]
  simp only [hs, Nat.reduceLT, if_false, Nat.reduceSub]
  rw [List.getElem?_append, hs]
  norm_num

theorem set_payload {A : Type} (z dom label : A) (state data : List A)
    (hs : state.length = 32) (hd : data.length ≤ 158) :
    List.setSlice! (state ++ dom :: label :: List.replicate 158 z) 34 data =
      state ++ dom :: label :: data ++
        List.replicate (158 - data.length) z := by
  have hbase :
      (state ++ dom :: label :: List.replicate 158 z).length = 192 := by
    simp only [List.length_append, hs, List.length_cons,
      List.length_replicate]
  have hprefix :
      List.take 34 (state ++ dom :: label :: List.replicate 158 z) =
        state ++ [dom, label] := by
    rw [List.take_append, hs, List.take_of_length_le (by omega)]
    norm_num
  have hdrop :
      List.drop (34 + data.length)
          (state ++ dom :: label :: List.replicate 158 z) =
        List.replicate (158 - data.length) z := by
    rw [List.drop_append, hs, List.drop_eq_nil_of_le (by omega)]
    simp only [List.nil_append]
    rw [show 34 + data.length - 32 = (data.length + 1) + 1 by omega,
      List.drop_succ_cons, List.drop_succ_cons]
    exact List.drop_replicate
  unfold List.setSlice!
  rw [hbase]
  simp only [Nat.reduceSub]
  rw [min_eq_left hd, List.take_length, hprefix, hdrop]
  simp only [List.append_assoc]
  rfl

theorem scratch_payload_window {A : Type} (z dom label : A)
    (state data : List A) (hs : state.length = 32)
    (hd : data.length ≤ 158) :
    List.slice 34 (34 + data.length)
        (state ++ dom :: label :: List.replicate 158 z) =
      List.replicate data.length z := by
  unfold List.slice
  have hdrop :
      List.drop 34 (state ++ dom :: label :: List.replicate 158 z) =
        List.replicate 158 z := by
    rw [List.drop_append, hs, List.drop_eq_nil_of_le (by omega)]
    norm_num
  rw [hdrop, show 34 + data.length - 34 = data.length by omega,
    List.take_replicate, min_eq_left hd]

theorem populated_prefix {A : Type} (z dom label : A)
    (state data : List A) (hs : state.length = 32) :
    List.slice 0 (34 + data.length)
        (state ++ dom :: label :: data ++
          List.replicate (158 - data.length) z) =
      state ++ dom :: label :: data := by
  unfold List.slice
  rw [List.drop_zero, show 34 + data.length - 0 = 34 + data.length by omega]
  let pre : List A := state ++ dom :: label :: data
  have hpre : pre.length = 34 + data.length := by
    simp only [pre, List.length_append, hs, List.length_cons]
    omega
  change List.take (34 + data.length)
    (pre ++ List.replicate (158 - data.length) z) = pre
  rw [List.take_append]
  rw [← hpre, List.take_length]
  simp only [Nat.sub_self, List.take_zero, List.append_nil]

theorem new_execution (H : Bytes → State) :
    AspisR137Transcript.transcript.Transcript.new (hashAdapter H) =
      ok (transcriptFor H zeroState) := by
  rfl

theorem profile_label :
    decodeByte AspisR137Transcript.transcript.label.PROFILE = ⟨1, by omega⟩ := by
  rw [AspisR137Transcript.transcript.label.PROFILE]
  apply Fin.ext
  rfl

theorem statement_label :
    decodeByte AspisR137Transcript.transcript.label.STATEMENT = ⟨2, by omega⟩ := by
  rw [AspisR137Transcript.transcript.label.STATEMENT]
  apply Fin.ext
  rfl

theorem root_label :
    decodeByte AspisR137Transcript.transcript.label.ROOT = ⟨3, by omega⟩ := by
  rw [AspisR137Transcript.transcript.label.ROOT]
  apply Fin.ext
  rfl

theorem second_phase_root_label :
    decodeByte AspisR137Transcript.transcript.label.SECOND_PHASE_ROOT =
      ⟨9, by omega⟩ := by
  rw [AspisR137Transcript.transcript.label.SECOND_PHASE_ROOT]
  apply Fin.ext
  rfl

theorem point_claims_label :
    decodeByte AspisR137Transcript.transcript.label.V6_POINT_CLAIMS =
      ⟨49, by omega⟩ := by
  rw [AspisR137Transcript.transcript.label.V6_POINT_CLAIMS]
  apply Fin.ext
  rfl

theorem dom_absorb_byte :
    decodeByte AspisR137Transcript.transcript.DOM_ABSORB = ⟨0, by omega⟩ := by
  rw [AspisR137Transcript.transcript.DOM_ABSORB]
  apply Fin.ext
  rfl

theorem packed_payload_limit :
    (AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize).val = 158 := by
  rw [AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
    Std.Usize.wrapping_sub_val_eq]
  have h192 : (192#usize : Std.Usize).val = 192 := rfl
  have h34 : (34#usize : Std.Usize).val = 34 := rfl
  rw [h192, h34]
  have hsize := (192#usize : Std.Usize).hSize
  have hrearrange :
      192 + (UScalar.size .Usize - 34) = 158 + UScalar.size .Usize := by
    omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem squeeze_execution
    (s : AspisR137Transcript.transcript.Transcript) :
    AspisR137Transcript.transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (SqueezeSourceExecution.message s.state 1#u8)
      let next ← s.hash (SqueezeSourceExecution.message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [AspisR137Transcript.transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat, Array.to_slice, Slice.length, Slice.len,
    core.slice.Slice.copy_from_slice, Array.from_slice, List.setSlice!,
    List.slice, Array.update, AspisR137Transcript.transcript.DOM_SQUEEZE,
    AspisR137Transcript.transcript.DOM_ADVANCE,
    SqueezeSourceExecution.message, SqueezeSourceExecution.frame, Array.make,
    lift, bind_tc_ok, hs, List.set_append, ht]

theorem squeeze_source_step (H : Bytes → State) (s : State) :
    AspisR137Transcript.transcript.Transcript.squeeze_block
        (transcriptFor H s) =
      .ok (encodeState (step H s).1, transcriptFor H (step H s).2) := by
  rw [squeeze_execution]
  simp only [transcriptFor, hashAdapter, squeeze_address, advance_address,
    bind_tc_ok, step]

theorem long_absorb_execution (H : Bytes → State) (s : State)
    (label : U8) (data : Slice U8)
    (long : ¬ data.len ≤
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize) :
    AspisR137Transcript.transcript.Transcript.absorb
        (transcriptFor H s) label data =
      ok (transcriptFor H
        (H (DuplexFrames.absorb (bytes s) (decodeByte label)
          (decodedSlice data)))) := by
  unfold AspisR137Transcript.transcript.Transcript.absorb
  simp only [lift, bind_tc_ok]
  rw [if_neg long]
  simp [transcriptFor, hashAdapter, decodedSlice, Array.to_slice, Array.make,
    flatten, encodeState, bytes, DuplexFrames.absorb, byte_roundtrip,
    dom_absorb_byte]

theorem short_absorb_execution (H : Bytes → State) (s : State)
    (label : U8) (data : Slice U8)
    (short : data.len ≤
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize) :
    AspisR137Transcript.transcript.Transcript.absorb
        (transcriptFor H s) label data =
      ok (transcriptFor H
        (H (DuplexFrames.absorb (bytes s) (decodeByte label)
          (decodedSlice data)))) := by
  have hs : (encodeState s).val.length = 32 := (encodeState s).property
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
  unfold AspisR137Transcript.transcript.Transcript.absorb
  simp only [lift, bind_tc_ok]
  rw [if_pos short]
  simp only [transcriptFor,
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
  simp only [setSlice_zero_repeat 0#u8 (encodeState s).val hs,
    List.length_append, hs, List.length_replicate, Array.getElem?_Usize_eq,
    h32val, h33val, scratch_slot32,
    bind_tc_ok, scratch_slot33_after_dom, set_frame_points, dif_pos]
  simp only [scratch_payload_window 0#u8
      AspisR137Transcript.transcript.DOM_ABSORB label (encodeState s).val
      data.val hs hd,
    List.length_replicate, bind_tc_ok,
    set_payload 0#u8 AspisR137Transcript.transcript.DOM_ABSORB label
      (encodeState s).val data.val hs hd,
    List.length_append, List.length_cons, hs, hfull, if_true, dif_pos,
    populated_prefix 0#u8 AspisR137Transcript.transcript.DOM_ABSORB label
      (encodeState s).val data.val hs]
  simp [hashAdapter, Array.make, flatten, encodeState, bytes,
    DuplexFrames.absorb, decodedSlice, byte_roundtrip, dom_absorb_byte]

#print axioms new_execution
#print axioms profile_label
#print axioms statement_label
#print axioms root_label
#print axioms second_phase_root_label
#print axioms point_claims_label
#print axioms dom_absorb_byte
#print axioms packed_payload_limit
#print axioms squeeze_execution
#print axioms squeeze_source_step
#print axioms long_absorb_execution
#print axioms short_absorb_execution

end AspisV8R19.R137TranscriptPrimitiveBridge
