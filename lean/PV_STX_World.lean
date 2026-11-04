import PV_STX_Machine
import PV_RJ4IDB_NativeTrace
/-! Port of PV_EVH_World.World and PV_EVH_Runtime.State into the continuation
machine. Additional resource cursors are source-level, not physical frames. -/
set_option autoImplicit false
namespace PV_STX_World
open Aeneas Aeneas.Std PV_STX_Machine
open PV_RJ4IDB (Bytes NativeEvent)
structure FileState where
  path : Bytes
  delivered : Bytes
  durable : Bytes
structure Base where
  entropyCursor : Nat := 0
  files : List FileState := []
  oracleHistory : List (Bytes × Bytes) := []
  attempts : Nat := 0
  retries : Nat := 0
  allocations : Nat := 0
  clockReads : Nat := 0
structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq
structure Block where
  identity : Nat
  address : Nat
  layout : Layout
  bytes : Bytes
  owner : Nat
structure Handle where
  identity : Nat
  path : Bytes
  cursor : Nat
  live : Bool
structure World where
  base : Base := {}
  heap : List Block := []
  nextIdentity : Nat := 0
  handles : List Handle := []
  allocator : Bytes := []
  errno : Int := 0
  stackCursor : Nat := 0
  threadCursor : Nat := 0

def ascii (s : String) : Bytes := s.toList.map (fun c => UInt8.ofNat c.toNat)
def side (tag : String) (payload : Bytes) : NativeEvent := .side (ascii tag) payload

def deliveredState (path bytes : Bytes) (w : World) : World :=
  if w.base.files.any (fun f => f.path == path) then
    {w with base := {w.base with files := w.base.files.map (fun f =>
      if f.path == path then {f with delivered := f.delivered ++ bytes} else f)}}
  else {w with base := {w.base with files := w.base.files ++ [⟨path,bytes,[]⟩]}}
def syncedState (path : Bytes) (w : World) : World :=
  {w with base := {w.base with files := w.base.files.map (fun f =>
    if f.path == path then {f with durable := f.delivered} else f)}}

theorem delivered_frame (path bytes : Bytes) (w : World) :
    (deliveredState path bytes w).heap = w.heap ∧
    (deliveredState path bytes w).allocator = w.allocator ∧
    (deliveredState path bytes w).base.entropyCursor = w.base.entropyCursor ∧
    (deliveredState path bytes w).handles = w.handles := by
  unfold deliveredState
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem synced_frame (path : Bytes) (w : World) :
    (syncedState path w).heap = w.heap ∧
    (syncedState path w).base.entropyCursor = w.base.entropyCursor := ⟨rfl,rfl⟩

/-- Local records: no static oracle/log and no precomputed whole-helper run. -/
structure CallRecord (Q A : Type) where
  request : Q
  before : World
  answer : Answer A
  after : World
  events : List NativeEvent

def record {Q A : Type} (request : Q) (before : World)
    (reply : Reply World NativeEvent A) : CallRecord Q A :=
  ⟨request,before,reply.answer,reply.world,reply.events⟩

#print axioms delivered_frame
#print axioms synced_frame
end PV_STX_World
