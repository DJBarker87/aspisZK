import AspisR1ProducerRelease47.Funs
import AspisR1ProducerRelease47.Interpolate48
import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Opening48
import AspisR1ProducerRelease47.Pairs
import AspisR1ProducerRelease47.Samples49
import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.EncoderNodes54
/-! Exact generic owner extraction, including the native CodeField trait and
M31/QM31 used method bodies. Unused inverse records are excluded explicitly. All reused arithmetic and carrier shapes are
checked byte-for-byte by bind-generic.py. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
structure scalar.CodeField (Self : Type) where
  ZERO : Result Self
  ONE : Result Self
  coremarkerCopyInst : core.marker.Copy Self
  corecmpEqInst : core.cmp.Eq Self
  from_m31 : field.M31 → Result Self
  add : Self → Self → Result Self
  sub : Self → Self → Result Self
  neg : Self → Result Self
  mul : Self → Self → Result Self
  try_inv : Self → Result (Option Self)

def generic54.collect
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E) (c : Slice E)
  (stride : Std.Usize) (offset : Std.Usize) (i : Std.Usize) (left : Std.Usize)
  (out : alloc.vec.Vec E) :
  Result (alloc.vec.Vec E)
  := do
  if left = 0#usize
  then ok out
  else
    let i1 ← lift (Std.Usize.wrapping_mul stride i)
    let i2 ← lift (Std.Usize.wrapping_add i1 offset)
    let t ← Slice.index_usize c i2
    let out1 ← alloc.vec.Vec.push out t
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i4 ← lift (Std.Usize.wrapping_sub left 1#usize)
    generic54.collect scalarCodeFieldInst c stride offset i3 i4 out1
partial_fixpoint

def generic54.eval_rec
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E) (c : Slice E)
  (depth : Std.Usize) (height : Std.Usize) (nodes : Array field.M31 9#usize) :
  Result E
  := do
  if height = 0#usize
  then Slice.index_usize c 0#usize
  else
    let i := Slice.len c
    let n ← i / 2#usize
    let even ←
      generic54.collect scalarCodeFieldInst c 2#usize 0#usize 0#usize n
        (alloc.vec.Vec.new E)
    let odd ←
      generic54.collect scalarCodeFieldInst c 2#usize 1#usize 0#usize n
        (alloc.vec.Vec.new E)
    let s := alloc.vec.Vec.deref even
    let i1 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i2 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let a ← generic54.eval_rec scalarCodeFieldInst s i1 i2 nodes
    let s1 := alloc.vec.Vec.deref odd
    let i3 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i4 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let b ← generic54.eval_rec scalarCodeFieldInst s1 i3 i4 nodes
    let m ← Array.index_usize nodes depth
    let t ← scalarCodeFieldInst.from_m31 m
    let t1 ← scalarCodeFieldInst.mul t b
    scalarCodeFieldInst.add a t1
partial_fixpoint

def generic54.channels
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E)
  (c : Array E 1024#usize) (nodes : Array field.M31 9#usize) :
  Result (Array E 4#usize)
  := do
  let s ← lift (Array.to_slice c)
  let a ←
    generic54.collect scalarCodeFieldInst s 4#usize 0#usize 0#usize 256#usize
      (alloc.vec.Vec.new E)
  let s1 ← lift (Array.to_slice c)
  let b ←
    generic54.collect scalarCodeFieldInst s1 4#usize 1#usize 0#usize 256#usize
      (alloc.vec.Vec.new E)
  let s2 ← lift (Array.to_slice c)
  let d ←
    generic54.collect scalarCodeFieldInst s2 4#usize 2#usize 0#usize 256#usize
      (alloc.vec.Vec.new E)
  let s3 ← lift (Array.to_slice c)
  let e ←
    generic54.collect scalarCodeFieldInst s3 4#usize 3#usize 0#usize 256#usize
      (alloc.vec.Vec.new E)
  let s4 := alloc.vec.Vec.deref a
  let t ← generic54.eval_rec scalarCodeFieldInst s4 0#usize 8#usize nodes
  let s5 := alloc.vec.Vec.deref b
  let t1 ← generic54.eval_rec scalarCodeFieldInst s5 0#usize 8#usize nodes
  let s6 := alloc.vec.Vec.deref d
  let t2 ← generic54.eval_rec scalarCodeFieldInst s6 0#usize 8#usize nodes
  let s7 := alloc.vec.Vec.deref e
  let t3 ← generic54.eval_rec scalarCodeFieldInst s7 0#usize 8#usize nodes
  ok (Array.make 4#usize [ t, t1, t2, t3 ])

def generic54.phi_inverse
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E) (x : E) (y : E)
  (h : Array E 4#usize) :
  Result (Array E 4#usize)
  := do
  let h0 ← Array.index_usize h 0#usize
  let h1 ← Array.index_usize h 1#usize
  let h2 ← Array.index_usize h 2#usize
  let h3 ← Array.index_usize h 3#usize
  let a ← scalarCodeFieldInst.mul y h1
  let b ← scalarCodeFieldInst.mul x h2
  let t ← scalarCodeFieldInst.mul x y
  let c ← scalarCodeFieldInst.mul t h3
  let t1 ← scalarCodeFieldInst.add h0 a
  let t2 ← scalarCodeFieldInst.add t1 b
  let t3 ← scalarCodeFieldInst.add t2 c
  let t4 ← scalarCodeFieldInst.sub h0 a
  let t5 ← scalarCodeFieldInst.add t4 b
  let t6 ← scalarCodeFieldInst.sub t5 c
  let t7 ← scalarCodeFieldInst.sub t4 b
  let t8 ← scalarCodeFieldInst.add t7 c
  let t9 ← scalarCodeFieldInst.sub t1 b
  let t10 ← scalarCodeFieldInst.sub t9 c
  ok (Array.make 4#usize [ t3, t6, t8, t10 ])

def generic54.encode_with_nodes
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E)
  (c : Array E 1024#usize) (nodes : Array field.M31 9#usize) (x : E) 
  (y : E) :
  Result (Array E 4#usize)
  := do
  let h ← generic54.channels scalarCodeFieldInst c nodes
  generic54.phi_inverse scalarCodeFieldInst x y h

def field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31
  (value : field.M31) : Result field.M31 := do
  let i ← value % field.P
  ok i

def field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.mul
  (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  field.M31.mul self rhs

def field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.sub
  (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  field.M31.sub self rhs

def field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.add
  (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  field.M31.add self rhs

def field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31
  (value : field.M31) : Result field.CM31 := do
  let m ← field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31 value
  field.CM31.from_m31 m

def field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31 value
  field.QM31.from_cm31 c

def field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  field.QM31.mul self rhs

def field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  field.QM31.sub self rhs

def field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  field.QM31.add self rhs

end AspisR1ProducerRelease47
