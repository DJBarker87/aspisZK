import Aeneas
import R1Z.PV_CBL_FallbackBlock
import R1Z.PV_CBL_FinalSoft
import R1Z.PV_CBL_ShaBytes
import R1Z.PV_CBL_ShaPadFixed
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_DigestSoft
def sha_update_soft_owned_loop.body
  (data : Slice Std.U8) (state : Array Std.U32 8#usize) (blocks : Std.U64)
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × Std.U64 × (Array Std.U8
    64#usize) × Std.Usize × Std.Usize) ((Array Std.U32 8#usize) × Std.U64 ×
    (Array Std.U8 64#usize) × Std.Usize))
  := do
  let i1 := Slice.len data
  if i < i1
  then
    let i2 ← Slice.index_usize data i
    let (_, index_mut_back) ← Array.index_mut_usize buffer pos
    let pos1 ← lift (Std.Usize.wrapping_add pos 1#usize)
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    if pos1 = 64#usize
    then
      let buffer1 := index_mut_back i2
      let state1 ← PV_CBL_FinalSoft.sha_compress_byte_owned state buffer1
      let blocks1 ← lift (core.num.U64.wrapping_add blocks 1#u64)
      ok (cont (state1, blocks1, buffer1, 0#usize, i3))
    else
      let buffer1 := index_mut_back i2
      ok (cont (state, blocks, buffer1, pos1, i3))
  else ok (done (state, blocks, buffer, pos))

def sha_update_soft_owned_loop
  (state : Array Std.U32 8#usize) (blocks : Std.U64)
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) (data : Slice Std.U8)
  (i : Std.Usize) :
  Result ((Array Std.U32 8#usize) × Std.U64 × (Array Std.U8 64#usize) ×
    Std.Usize)
  := do
  loop
    (fun (state1, blocks1, buffer1, pos1, i1) =>
      sha_update_soft_owned_loop.body data state1 blocks1 buffer1 pos1 i1)
    (state, blocks, buffer, pos, i)

def sha_update_soft_owned
  (state : Array Std.U32 8#usize) (blocks : Std.U64)
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) (data : Slice Std.U8) :
  Result ((Array Std.U32 8#usize) × Std.U64 × (Array Std.U8 64#usize) ×
    Std.Usize)
  := do
  sha_update_soft_owned_loop state blocks buffer pos data 0#usize

def sha_default_soft_owned
  :
  Result ((Array Std.U32 8#usize) × Std.U64 × (Array Std.U8 64#usize) ×
    Std.Usize)
  := do
  let a := Array.repeat 64#usize 0#u8
  ok
    (Array.make 8#usize [
       1779033703#u32, 3144134277#u32, 1013904242#u32, 2773480762#u32,
       1359893119#u32, 2600822924#u32, 528734635#u32, 1541459225#u32
       ], 0#u64, a, 0#usize)

def sha_digest_soft_owned
  (data : Slice Std.U8) : Result (Array Std.U8 32#usize) := do
  let (state, blocks, buffer, pos) ← sha_default_soft_owned
  let (state1, blocks1, buffer1, pos1) ←
    sha_update_soft_owned state blocks buffer pos data
  let (digest, _, _, _) ← PV_CBL_FinalSoft.sha_finalize_soft_owned state1 blocks1 buffer1 pos1
  ok digest

#print axioms sha_update_soft_owned_loop.body
#print axioms sha_update_soft_owned_loop
#print axioms sha_update_soft_owned
#print axioms sha_default_soft_owned
#print axioms sha_digest_soft_owned
end PV_CBL_DigestSoft
