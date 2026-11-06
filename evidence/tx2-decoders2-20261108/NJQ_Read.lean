import NJI_PolicyParser
set_option autoImplicit false
noncomputable section
namespace NJQ_Read
open Aeneas Aeneas.Std Result
/-- Hand reference for the Rust range/try_into/unwrap sequence; exact P7 calls. -/
def read (b : Slice U8) (off n : Usize) : Result (Array U8 n) := do
 let stop ← off+n
 let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   b {start:=off,«end»:=stop}
 let converted ← core.array.TryFromArrayCopySlice.try_from n core.marker.CopyU8 bytes
 core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted

theorem value (b : Slice U8) (off n : Usize) (fit : off.val+n.val≤b.val.length) :
 read b off n = ok (NHY_NaturalReads.array b off.val n fit) := by
 obtain ⟨stop,call,value,range⟩ := NHY_FieldRead.range b off n fit
 have cast := NHY_ExactArray.cast n (NHY_SliceRead.segment b off.val n.val)
   (NHY_NaturalReads.array b off.val n fit) rfl
 simp only [read,call,bind_tc_ok,range,cast,core.result.Result.unwrap]

theorem zero_eq (n : Usize) (a : Array U8 n) :
 a=Array.repeat n 0#u8 ↔ a.val=List.replicate n.val 0#u8 := by
 constructor
 · intro h;exact congrArg Subtype.val h
 · intro h;exact Subtype.ext h

#print axioms zero_eq
#print axioms value
end NJQ_Read
