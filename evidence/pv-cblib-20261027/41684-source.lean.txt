-- Exact extracted fixed-size safe padding reference; Types empty.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_ShaPadFixed
/-- [pv_cblib_source::sha_pad_zero]: loop body 0:
    Source: 'lib.rs', lines 423:4-423:34
    Visibility: public -/
@[rust_loop_body]
def sha_pad_zero_loop.body
  (buffer : Array Std.U8 64#usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U8 64#usize) × Std.Usize) (Array Std.U8
    64#usize))
  := do
  if i < 64#usize
  then
    let buffer1 ← Array.update buffer i 0#u8
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (buffer1, i1))
  else ok (done buffer)

/-- [pv_cblib_source::sha_pad_zero]: loop 0:
    Source: 'lib.rs', lines 423:4-423:34
    Visibility: public -/
@[rust_loop]
def sha_pad_zero_loop
  (buffer : Array Std.U8 64#usize) (i : Std.Usize) :
  Result (Array Std.U8 64#usize)
  := do
  loop
    (fun (buffer1, i1) => sha_pad_zero_loop.body buffer1 i1)
    (buffer, i)

/-- [pv_cblib_source::sha_pad_zero]:
    Source: 'lib.rs', lines 420:0-425:1
    Visibility: public -/
def sha_pad_zero
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) :
  Result (Array Std.U8 64#usize)
  := do
  let buffer1 ← Array.update buffer pos 128#u8
  let i ← lift (Std.Usize.wrapping_add pos 1#usize)
  sha_pad_zero_loop buffer1 i

/-- [pv_cblib_source::sha_pad_suffix8]:
    Source: 'lib.rs', lines 443:0-448:1
    Visibility: public -/
def sha_pad_suffix8
  (buffer : Array Std.U8 64#usize) (suffix : Array Std.U8 8#usize) :
  Result (Array Std.U8 64#usize)
  := do
  let a ← Array.index_usize suffix 0#usize
  let b ← Array.index_usize suffix 1#usize
  let c ← Array.index_usize suffix 2#usize
  let d ← Array.index_usize suffix 3#usize
  let e ← Array.index_usize suffix 4#usize
  let f ← Array.index_usize suffix 5#usize
  let g ← Array.index_usize suffix 6#usize
  let h ← Array.index_usize suffix 7#usize
  let buffer1 ← Array.update buffer 56#usize a
  let buffer2 ← Array.update buffer1 57#usize b
  let buffer3 ← Array.update buffer2 58#usize c
  let buffer4 ← Array.update buffer3 59#usize d
  let buffer5 ← Array.update buffer4 60#usize e
  let buffer6 ← Array.update buffer5 61#usize f
  let buffer7 ← Array.update buffer6 62#usize g
  Array.update buffer7 63#usize h

/-- [pv_cblib_source::sha_pad_owned_split8]:
    Source: 'lib.rs', lines 449:0-459:1
    Visibility: public -/
def sha_pad_owned_split8
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize)
  (suffix : Array Std.U8 8#usize) :
  Result ((Array Std.U8 64#usize) × (Option (Array Std.U8 64#usize)) × (Array
    Std.U8 64#usize) × Std.Usize)
  := do
  let head ← sha_pad_zero buffer pos
  let i ← lift (Std.Usize.wrapping_sub 64#usize pos)
  let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
  if i1 < 8#usize
  then
    let a := Array.repeat 64#usize 0#u8
    let second ← sha_pad_suffix8 a suffix
    ok (head, some second, head, 0#usize)
  else
    let first ← sha_pad_suffix8 head suffix
    ok (first, none, first, 0#usize)

#print axioms sha_pad_zero_loop.body
#print axioms sha_pad_zero_loop
#print axioms sha_pad_zero
#print axioms sha_pad_suffix8
#print axioms sha_pad_owned_split8
end PV_CBL_ShaPadFixed
