import Aeneas
set_option autoImplicit false
namespace PDict_TapeSource244
open Aeneas Aeneas.Std Result ControlFlow Error

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

#print axioms world.Reply.Insts.CoreCloneClone.clone
#print axioms world.Tape.Insts.CoreCloneClone.clone
#print axioms world.next
#print axioms world.retry_collision
end PDict_TapeSource244
