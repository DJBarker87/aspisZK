import Aeneas
import R1Z.PDict_RowTable244
set_option autoImplicit false
namespace PDict_OwnedSource244
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [aspis_r1_cost_probe::transport::Variant]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-r1-cost-probe/src/transport.rs', lines 3:0-3:16
    Name pattern: [aspis_r1_cost_probe::transport::Variant]
    Visibility: public -/
@[discriminant isize, rust_type "aspis_r1_cost_probe::transport::Variant"]
inductive aspis_r1_cost_probe.transport.Variant where
| S1 : aspis_r1_cost_probe.transport.Variant
| S2 : aspis_r1_cost_probe.transport.Variant
| D : aspis_r1_cost_probe.transport.Variant

/-- [pdict_world244::world::Reply]
    Source: 'world.rs', lines 4:0-4:70
    Visibility: public -/
structure world.Reply where
  operation : Std.U8
  value : Std.I32
  error : Std.I32

/-- [pdict_world244::world::Tape]
    Source: 'world.rs', lines 6:0-6:61
    Visibility: public -/
structure world.Tape where
  replies : Array world.Reply 16#usize
  used : Std.Usize

/-- [pdict_world244::world::Outcome]
    Source: 'world.rs', lines 7:0-7:63
    Visibility: public -/
structure world.Outcome where
  tape : world.Tape
  reply : Option world.Reply


/-- [pdict_world244::row::ORDER]
    Source: 'row.rs', lines 4:0-69:2 -/
@[global_simps, irreducible]
def row.ORDER : Array Std.U16 1024#usize := R1Z.PDict_RowTable244.table

/-- [pdict_world244::row::row]:
    Source: 'row.rs', lines 70:0-77:1
    Visibility: public -/
def row.row
  (variant : aspis_r1_cost_probe.transport.Variant) (j : Std.Usize) :
  Result Std.Usize
  := do
  match variant with
  | aspis_r1_cost_probe.transport.Variant.S1 =>
    let i ← lift (j &&& 3#usize)
    let i1 ← lift (Std.Usize.wrapping_shl i 6#u32)
    let i2 ← lift (Std.Usize.wrapping_shr j 2#u32)
    let i3 ← lift (i2 &&& 3#usize)
    let i4 ← lift (Std.Usize.wrapping_shl i3 8#u32)
    let i5 ← lift (i1 ||| i4)
    let i6 ← lift (Std.Usize.wrapping_shr j 4#u32)
    let i7 ← lift (i6 &&& 3#usize)
    let i8 ← lift (Std.Usize.wrapping_shl i7 4#u32)
    let i9 ← lift (i5 ||| i8)
    let i10 ← lift (Std.Usize.wrapping_shr j 6#u32)
    let i11 ← lift (i10 &&& 3#usize)
    let i12 ← lift (i9 ||| i11)
    let i13 ← lift (Std.Usize.wrapping_shr j 8#u32)
    let i14 ← lift (i13 &&& 3#usize)
    let i15 ← lift (Std.Usize.wrapping_shl i14 2#u32)
    ok (i12 ||| i15)
  | aspis_r1_cost_probe.transport.Variant.S2 =>
    let i ← lift (j &&& 3#usize)
    let i1 ← lift (Std.Usize.wrapping_shl i 6#u32)
    let i2 ← lift (Std.Usize.wrapping_shr j 2#u32)
    let i3 ← lift (i2 &&& 3#usize)
    let i4 ← lift (Std.Usize.wrapping_shl i3 8#u32)
    let i5 ← lift (i1 ||| i4)
    let i6 ← lift (Std.Usize.wrapping_shr j 4#u32)
    let i7 ← lift (i6 &&& 3#usize)
    let i8 ← lift (Std.Usize.wrapping_shl i7 4#u32)
    let i9 ← lift (i5 ||| i8)
    let i10 ← lift (Std.Usize.wrapping_shr j 6#u32)
    let i11 ← lift (i10 &&& 3#usize)
    let i12 ← lift (i9 ||| i11)
    let i13 ← lift (Std.Usize.wrapping_shr j 8#u32)
    let i14 ← lift (i13 &&& 3#usize)
    let i15 ← lift (Std.Usize.wrapping_shl i14 2#u32)
    ok (i12 ||| i15)
  | aspis_r1_cost_probe.transport.Variant.D =>
    let i ← Array.index_usize row.ORDER j
    ok (UScalar.cast .Usize i)

/-- [pdict_world244::coefficients::owned]: loop body 0:
    Source: 'coefficients.rs', lines 10:4-13:5
    Visibility: public -/
@[rust_loop_body]
def coefficients.owned_loop.body
  {T : Type} (variant : aspis_r1_cost_probe.transport.Variant)
  (rows : Array T 1024#usize) (out : Array T 1024#usize) (index : Std.Usize) :
  Result (ControlFlow ((Array T 1024#usize) × Std.Usize) (Array T 1024#usize))
  := do
  if index < 1024#usize
  then
    let i ← row.row variant index
    let t ← Array.index_usize rows i
    let out1 ← Array.update out index t
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (out1, index1))
  else ok (done out)

/-- [pdict_world244::coefficients::owned]: loop 0:
    Source: 'coefficients.rs', lines 10:4-13:5
    Visibility: public -/
@[rust_loop]
def coefficients.owned_loop
  {T : Type} (variant : aspis_r1_cost_probe.transport.Variant)
  (rows : Array T 1024#usize) (out : Array T 1024#usize) (index : Std.Usize) :
  Result (Array T 1024#usize)
  := do
  loop
    (fun (out1, index1) => coefficients.owned_loop.body variant rows out1
      index1)
    (out, index)

/-- [pdict_world244::coefficients::owned]:
    Source: 'coefficients.rs', lines 7:0-15:1
    Visibility: public -/
@[reducible]
def coefficients.owned
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (variant : aspis_r1_cost_probe.transport.Variant) (rows : Array T 1024#usize)
  :
  Result (Array T 1024#usize)
  := do
  coefficients.owned_loop variant rows rows 0#usize

/-- [pdict_world244::coefficients::copy_owned]: loop body 0:
    Source: 'coefficients.rs', lines 21:4-24:5
    Visibility: public -/
@[rust_loop_body]
def coefficients.copy_owned_loop.body
  {T : Type} (rows : Array T 1024#usize) (out : Array T 1024#usize)
  (index : Std.Usize) :
  Result (ControlFlow ((Array T 1024#usize) × Std.Usize) (Array T 1024#usize))
  := do
  if index < 1024#usize
  then
    let t ← Array.index_usize rows index
    let out1 ← Array.update out index t
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (out1, index1))
  else ok (done out)

/-- [pdict_world244::coefficients::copy_owned]: loop 0:
    Source: 'coefficients.rs', lines 21:4-24:5
    Visibility: public -/
@[rust_loop]
def coefficients.copy_owned_loop
  {T : Type} (rows : Array T 1024#usize) (out : Array T 1024#usize)
  (index : Std.Usize) :
  Result (Array T 1024#usize)
  := do
  loop
    (fun (out1, index1) => coefficients.copy_owned_loop.body rows out1 index1)
    (out, index)

/-- [pdict_world244::coefficients::copy_owned]:
    Source: 'coefficients.rs', lines 18:0-26:1
    Visibility: public -/
@[reducible]
def coefficients.copy_owned
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (rows : Array T 1024#usize) :
  Result (Array T 1024#usize)
  := do
  coefficients.copy_owned_loop rows rows 0#usize

/-- [pdict_world244::world::{impl core::clone::Clone for pdict_world244::world::Reply}::clone]:
    Source: 'world.rs', lines 3:9-3:14
    Visibility: public -/
def world.Reply.Insts.CoreCloneClone.clone
  (self : world.Reply) : Result world.Reply := do
  ok self

/-- Trait implementation: [pdict_world244::world::{impl core::clone::Clone for pdict_world244::world::Reply}]
    Source: 'world.rs', lines 3:9-3:14 -/
@[reducible]
def world.Reply.Insts.CoreCloneClone : core.clone.Clone world.Reply := {
  clone := world.Reply.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [pdict_world244::world::{impl core::marker::Copy for pdict_world244::world::Reply}]
    Source: 'world.rs', lines 3:16-3:20 -/
@[reducible]
def world.Reply.Insts.CoreMarkerCopy : core.marker.Copy world.Reply := {
  cloneInst := world.Reply.Insts.CoreCloneClone
}

/-- [pdict_world244::world::{impl core::clone::Clone for pdict_world244::world::Tape}::clone]:
    Source: 'world.rs', lines 5:9-5:14
    Visibility: public -/
def world.Tape.Insts.CoreCloneClone.clone
  (self : world.Tape) : Result world.Tape := do
  ok self

/-- Trait implementation: [pdict_world244::world::{impl core::clone::Clone for pdict_world244::world::Tape}]
    Source: 'world.rs', lines 5:9-5:14 -/
@[reducible]
def world.Tape.Insts.CoreCloneClone : core.clone.Clone world.Tape := {
  clone := world.Tape.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [pdict_world244::world::{impl core::marker::Copy for pdict_world244::world::Tape}]
    Source: 'world.rs', lines 5:16-5:20 -/
@[reducible]
def world.Tape.Insts.CoreMarkerCopy : core.marker.Copy world.Tape := {
  cloneInst := world.Tape.Insts.CoreCloneClone
}

/-- [pdict_world244::world::next]:
    Source: 'world.rs', lines 9:0-15:1
    Visibility: public -/
def world.next
  (tape : world.Tape) (operation : Std.U8) : Result world.Outcome := do
  if tape.used >= 16#usize
  then ok { tape, reply := none }
  else
    let reply ← Array.index_usize tape.replies tape.used
    if reply.operation != operation
    then ok { tape, reply := none }
    else
      let i ← lift (Std.Usize.wrapping_add tape.used 1#usize)
      ok { tape := { tape with used := i }, reply := (some reply) }

/-- [pdict_world244::world::retry_collision]:
    Source: 'world.rs', lines 18:0-18:58
    Visibility: public -/
def world.retry_collision (errno : Std.I32) : Result Bool := do
  ok (errno = 17#i32)

#print axioms row.ORDER
#print axioms row.row
#print axioms coefficients.owned_loop.body
#print axioms coefficients.owned_loop
#print axioms coefficients.owned
#print axioms coefficients.copy_owned_loop.body
#print axioms coefficients.copy_owned_loop
#print axioms coefficients.copy_owned
#print axioms world.Reply.Insts.CoreCloneClone.clone
#print axioms world.Tape.Insts.CoreCloneClone.clone
#print axioms world.next
#print axioms world.retry_collision
end PDict_OwnedSource244
