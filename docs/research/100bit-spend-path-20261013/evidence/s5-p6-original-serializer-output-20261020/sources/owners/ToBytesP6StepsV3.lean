import AspisR1WideToBytesSource.Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace P6ToBytes.Steps
open AspisR1WideToBytesSource
abbrev ChunkIt := core.slice.iter.ChunksExactMut Std.U8
abbrev LimbIt := core.array.iter.IntoIter Std.U32 8#usize
abbrev Zip := core.iter.adapters.zip.Zip ChunkIt LimbIt
abbrev Back := Zip → Zip

def sourceLimbs (x : field.wide_exact.WideExact) : List Std.U32 :=
  [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
   x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]

theorem u32BytesLen (w : Std.U32) : (core.num.U32.to_le_bytes w).val.length = 4 := by
  have h := (core.num.U32.to_le_bytes w).property
  change (core.num.U32.to_le_bytes w).val.length = 4 at h
  exact h

theorem arraySliceLen {α : Type} {n : Usize} (a : Array α n) :
    Slice.len (Array.to_slice a) = n := by
  apply UScalar.eq_of_val_eq
  simp [Slice.len, Array.to_slice, a.property]

theorem fourZeroSliceLen :
    Slice.len (⟨[0#u8,0#u8,0#u8,0#u8], by scalar_tac⟩ : Slice Std.U8) = 4#usize := by
  apply UScalar.eq_of_val_eq
  simp [Slice.len]

def initSlice : Slice Std.U8 := Array.to_slice (Array.repeat 32#usize 0#u8)
def initChunkIt : ChunkIt := ⟨initSlice,4#usize,0,0#usize,false⟩
def initLimbIt (x : field.wide_exact.WideExact) : LimbIt := ⟨sourceLimbs x,0⟩
def initZip (x : field.wide_exact.WideExact) : Zip := ⟨initChunkIt,initLimbIt x⟩
def step (s : Zip × Back) : Result (ControlFlow (Zip × Back) Back) :=
  field.wide_exact.WideExact.to_le_bytes_loop.body s.1 s.2

theorem initial_step_cont (x : field.wide_exact.WideExact) :
    ∃ s, step (initZip x, fun z => z) = .ok (.cont s) := by
  dsimp [step, initZip, initChunkIt, initSlice, initLimbIt]
  simp [lift, bind_tc_ok, sourceLimbs, field.wide_exact.WideExact.to_le_bytes_loop.body,
    P6ToBytes.StdModel.zipNext,
    P6ToBytes.StdModel.MutableIterator.zip.trait_default,
    P6ToBytes.StdModel.MutableIterator,
    Aeneas.Std.core.slice.Slice.chunks_exact_mut,
    Aeneas.Std.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    Aeneas.Std.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.slice.Slice.copy_from_slice,
    Array.to_slice, Slice.len, u32BytesLen, arraySliceLen, fourZeroSliceLen,
    UScalar.ofNatCore_val_eq]

#print axioms initial_step_cont
end P6ToBytes.Steps
