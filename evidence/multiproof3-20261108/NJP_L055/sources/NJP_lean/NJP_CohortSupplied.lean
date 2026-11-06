import NJP_CohortOccupied
import MultiproofConeNodeWindow

set_option autoImplicit false
noncomputable section
namespace NJP_CohortSupplied
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.MultiproofConePhysicalProgram

def supplied (s : reference.Scratch) (physical : Slice U8) (ni : Usize)
    (index : U32) (value : RefDigest) (w : Usize) :=
 checked (Slice.len physical-s.«at») fun remaining =>
 if remaining<32#usize then .done (.ok (.Stop s)) else
 checked (s.«at»+32#usize) fun cursor =>
 checked (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   physical {start:=s.«at»,«end»:=cursor}) fun chunk =>
 checked (reference.read32 chunk) fun sibling =>
 if index &&& 1#u32=0#u32 then writer s value sibling ni cursor index w
 else writer s sibling value ni cursor index w

theorem missing (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (physical : Slice U8) (ni : Usize) (index : U32) (value : RefDigest) (w : Usize)
    (cursor : s.«at».val≤physical.val.length) (short : physical.val.length<s.«at».val+32) :
 eval H (supplied s physical ni index value w)=([],ok (.Stop s)) := by
 obtain ⟨remaining,subtraction,remaining_value⟩ := NJP_CheckedWords.subtract
   (Slice.len physical) s.«at» (by simpa only [Slice.len_val] using cursor)
 have small : remaining<32#usize := by change remaining.val<32; rw [remaining_value]; change physical.val.length-s.«at».val<32;omega
 unfold supplied
 rw [subtraction]
 simp only [checked,if_pos small,eval]

theorem available (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (physical : Slice U8) (i ni w : Usize)
    (next_value : ni.val=i.val+1) (ib : i.val<16) (wb : w.val<16)
    (enough : s.«at».val+32≤physical.val.length) :
 let result := eval H (supplied s physical ni (s.idx.val[i.val]!) (s.val.val[i.val]!) w)
 (result.1,mapResult projectRow result.2)=
 let request := NJP_RowModel.siblingRequest (raw s) i.val (fun n => physical.val[n]!)
 ([(NJP_RequestTransport.address request,H (NJP_RequestTransport.address request))],
  ok (.next (NJP_RowModel.write (raw s) i.val w.val (s.«at».val+32)
       (decode (H (NJP_RequestTransport.address request)))) (i.val+1) (w.val+1))) := by
 obtain ⟨remaining,subtraction,remaining_value⟩ := NJP_CheckedWords.subtract
   (Slice.len physical) s.«at» (by change s.«at».val≤physical.val.length;omega)
 have large : ¬remaining<32#usize := by change ¬remaining.val<32;rw [remaining_value];change ¬physical.val.length-s.«at».val<32;omega
 obtain ⟨cursor,chunk,view,addition,cursor_value,rangeEq,readEq,chunk_value⟩ :=
   AspisR1.MultiproofConeNodeWindow.physical_read physical s.«at» enough
 have chunk_eq : chunk=encode (NJP_RowModel.window (fun n => physical.val[n]!) s.«at».val) := by
   apply Subtype.ext
   rw [chunk_value,NJP_WindowCarrier.contents physical s.«at».val enough]
   rfl
 dsimp only
 unfold supplied
 rw [subtraction]
 simp only [checked,if_neg large]
 rw [addition]
 simp only [checked]
 rw [rangeEq]
 simp only [checked]
 rw [readEq]
 simp only [checked]
 have parity : (s.idx.val[i.val]! &&& 1#u32=0#u32) ↔ NJP_RowModel.index (raw s) i.val%2=0 := by
   constructor
   · intro h
     have v := congrArg UScalar.val h
     rw [NJP_CohortRead.parity,←NJP_CohortRead.index s i ib] at v
     exact v
   · intro h
     apply UScalar.eq_of_val_eq
     rw [NJP_CohortRead.parity,←NJP_CohortRead.index s i ib,h]
     rfl
 by_cases even : NJP_RowModel.index (raw s) i.val%2=0
 · rw [if_pos (parity.mpr even)]
   rw [NJP_CohortWrite.writer H s _ _ ni cursor _ i w wb (NJP_CohortRead.index s i ib).symm]
   simp only [NJP_RowModel.siblingRequest,if_pos even,NJP_RequestTransport.address,
     NJP_CohortRead.value s i ib,encode_decode,chunk_eq,next_value,cursor_value,raw]
 · rw [if_neg (fun h => even (parity.mp h))]
   rw [NJP_CohortWrite.writer H s _ _ ni cursor _ i w wb (NJP_CohortRead.index s i ib).symm]
   simp only [NJP_RowModel.siblingRequest,if_neg even,NJP_RequestTransport.address,
     NJP_CohortRead.value s i ib,encode_decode,chunk_eq,next_value,cursor_value,raw]

#print missing
#print axioms missing
#print available
#print axioms available
end NJP_CohortSupplied
end
