import R1Z.PV_RDEA_AppendNoGrowth
import R1Z.PV_CBL_AppendSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_AppendSimulation
open PV_CBL_StringBytesAdapter PV_RDB1_V183_ReserveWorld

theorem map_ok (xs : List U8) :
    List.mapM (fun b : U8 => (ok b : Result U8)) xs = ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, ih, bind_tc_ok]; rfl

theorem clone_bytes (s : Slice U8) :
    Slice.clone core.clone.CloneU8.clone s=ok s := by
  change Slice.clone (fun x : U8 => ok x) s=ok s
  unfold Slice.clone List.clone
  split <;> rename_i h
  all_goals have hh := map_ok s.val
  all_goals rw [hh] at h
  all_goals cases h
  rfl

theorem callback_bytes (s : String) (t : Str)
    (bound : (encodeList s).length+t.val.length≤Usize.max) :
    append s t=decode ⟨encodeList s++t.val,by rw [List.length_append]; exact bound⟩ := by
  have input : (encodeList s).length≤Usize.max := by omega
  simp only [append, encode, dif_pos input, bind_tc_ok,
    PV_CBL_StringPushBytes.push_bytes_reference, alloc.vec.Vec.extend_from_slice]
  simp only [alloc.vec.Vec.length, Slice.length, dif_pos bound]
  split <;> rename_i h
  all_goals have hh := clone_bytes (t : Slice U8)
  all_goals rw [hh] at h
  all_goals cases h
  rfl

/-- A representation relation records bytes and capacity separately; the
extracted String alone does not carry the physical allocation header. -/
def Represents (s : String) (b : Buffer U8) : Prop := b.values=encodeList s

theorem empty_represents (b : Buffer U8) (empty : b.values=[]) : Represents "" b := by
  exact empty

theorem encode_append (s t : String) : encodeList (s++t)=encodeList s++encodeList t := by
  simp only [encodeList, String.toByteArray_append, ByteArray.data_append,
    Array.toList_append, List.map_append]

theorem callback_value (s text : String) (t : Str)
    (tailbytes : t.val=encodeList text)
    (bound : (encodeList s).length+t.val.length≤Usize.max) :
    append s t=ok (s++text) := by
  rw [callback_bytes s t bound]
  apply PV_CBL_StringByteObservation.decode_of_bytes
  change encodeList s++t.val=encodeList (s++text)
  rw [tailbytes,encode_append]

theorem physical_callback {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (w : World S F)
    (s text : String) (t : Str) (repr : Represents s b)
    (tailbytes : t.val=encodeList text)
    (fits : b.values.length+t.val.length≤b.capacity) (cap : b.capacity≤Usize.max) :
    let out := PV_RDEA_AppendNoGrowth.appended b t.val fits
    let after : World S F := {w with memory:=PV_RDB1_Append.writeTail b.address b.values.length t.val w.memory}
    PV_RDEA_AppendExecution.append step shape b t.val w=(.ok out,after) ∧
    append s t=ok (s++text) ∧ Represents (s++text) out ∧
    after.allocator=w.allocator ∧ after.history=w.history ∧
    after.frame=w.frame ∧ out.address=b.address ∧ out.capacity=b.capacity := by
  dsimp only
  refine ⟨PV_RDEA_AppendNoGrowth.complete step shape b t.val w fits,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · apply callback_value s text t tailbytes
    change b.values=encodeList s at repr
    rw [←repr]
    omega
  · change b.values++t.val=encodeList (s++text)
    rw [encode_append,←repr,tailbytes]

#print axioms encode_append
#print axioms callback_value
#print axioms physical_callback
#print axioms map_ok
#print axioms clone_bytes
#print axioms callback_bytes
#print axioms empty_represents
end R1Z.PV_RDEAC_AppendSimulation
