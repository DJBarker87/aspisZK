import MultiproofConePhysicalAddress
import MultiproofConePhysicalLive
import MultiproofConeNodeWindow

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalViews
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalLive MultiproofConePhysicalTransport
open MultiproofConeLiveOrder MultiproofConeLivePreservation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def decodeEntry (e : Entry) : Nat × State := (e.1,decodeState e.2)
def live (s : reference.Scratch) (start count : Nat) : OraclePortFrozenOrder.Live :=
  (view s start count).map decodeEntry

def remaining (physical : Slice U8) (cursor : Usize) : Bytes :=
  MultiproofConeCanonical.bytesOf (physical.val.drop cursor.val)

theorem view_cons (s : reference.Scratch) (start count : Nat) :
    view s start (count+1)=cell s start::view s (start+1) count := by
  simp only [view,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j mem
  simp only [Function.comp_apply]
  congr 1
  omega

theorem live_cons (s : reference.Scratch) (start count : Nat) :
    live s start (count+1)=decodeEntry (cell s start)::live s (start+1) count := by
  rw [live,view_cons,List.map_cons];rfl

theorem live_empty (s : reference.Scratch) (start : Nat) : live s start 0=[] := rfl

theorem live_sorted (s : reference.Scratch) (n : Nat) (sorted : Strict (keys s) 0 n) :
    ((live s 0 n).map Prod.fst).Pairwise (·<·) := by
  apply List.pairwise_iff_getElem.mpr
  intro a b ha hb ab
  simp only [live,view,List.length_map,List.length_range] at ha hb
  simp only [live,view,List.map_map,List.getElem_map,List.getElem_range,Function.comp_apply,
    decodeEntry,cell,Nat.zero_add]
  exact sorted a b (by omega) ab hb

theorem live_unread (s : reference.Scratch) (w : Usize) (parent : U32)
    (digest : MultiproofConePhysicalProgram.Digest) (cursor : Usize) (wb : w.val<16)
    (start count : Nat) (safe : w.val<start) (last : start+count≤16) :
    live {s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor} start count=live s start count := by
  rw [live,unread s w parent digest cursor wb start count safe last];rfl

theorem remaining_step (physical : Slice U8) (before after : Usize)
    (advance : after.val=before.val+32) :
    (remaining physical before).drop 32=remaining physical after := by
  simp only [remaining,MultiproofConeCanonical.bytesOf,List.map_drop,List.drop_drop,advance,Nat.add_comm]

theorem sibling_decode (physical : Slice U8) (cursor : Usize)
    (sibling : MultiproofConePhysicalProgram.Digest)
    (content : sibling.val=(physical.val.drop cursor.val).take 32) :
    SemanticRecordCodec.decodeState ((remaining physical cursor).take 32)=some (decodeState sibling) := by
  have eq : (remaining physical cursor).take 32=bytes (decodeState sibling) := by
    rw [digest_bytes]
    simp only [remaining,MultiproofConeCanonical.bytesOf,List.map_take,content]
  rw [eq,SemanticRecordCodec.decodeState_bytes]

#print axioms view_cons
#print axioms live_cons
#print axioms live_empty
#print axioms live_sorted
#print axioms live_unread
#print axioms remaining_step
#print axioms sibling_decode
end AspisR1.MultiproofConePhysicalViews
