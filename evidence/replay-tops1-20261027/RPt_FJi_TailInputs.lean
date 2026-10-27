import RPt_FJi_Inputs
import RPt_FIo_FieldBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_TailInputs
open Aeneas Aeneas.Std Result
open FJi_Accumulations
open FIo_FieldBridge (NQ)
/-- Exactly the first installed tail read, following g[28]. -/
def read0 (q : Array U8 608#usize) (slot : Usize) : Result NQ := do
  let base ← slot*120#usize
  let start ← base+104#usize
  let stop ← base+120#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start,«end»:=stop}
  let o ← FIp_DotDecode.field.QM31.from_le_bytes s
  core.option.Option.unwrap o
/-- Exactly the second installed tail read, following g[26]. -/
def read1 (q : Array U8 608#usize) (slot : Usize) : Result NQ := do
  let delta ← slot*32#usize
  let base ← 480#usize+delta
  let off ← 0#usize*16#usize
  let start ← base+off
  let stop ← start+16#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start,«end»:=stop}
  let o ← FIp_DotDecode.field.QM31.from_le_bytes s
  core.option.Option.unwrap o
/-- Exactly the third installed tail read, following g[27]. -/
def read2 (q : Array U8 608#usize) (slot : Usize) : Result NQ := do
  let delta ← slot*32#usize
  let base ← 480#usize+delta
  let off ← 1#usize*16#usize
  let start ← base+off
  let stop ← start+16#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start,«end»:=stop}
  let o ← FIp_DotDecode.field.QM31.from_le_bytes s
  core.option.Option.unwrap o

def observed (r : Result NQ) : NQ := match r with
  | .ok x => x
  | _ => FIo_Native.aspis_core.field.QM31.ZERO

theorem observed_value (r : Result NQ) (x : NQ) (run : r=ok x) : observed r=x := by
  simp only [observed,run]
#print axioms observed_value
end AspisR1.FJi_TailInputs
end
