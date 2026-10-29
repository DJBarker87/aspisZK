import R1Z.PV_OWNB_LinkCodec
import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWNB_Cursor
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link PV_OWNB_LinkCodec
/-- Exclusive internal cursor scope; caller ownership is retained until transfer.
The source unread interval and destination prefix share the same generation. -/
structure Cursor where
 memory : Memory
 token : Token
 owner : Nat
 cell : Cell
 read : Nat
 written : Nat
 length : Nat
 capacity : Nat
 source : Nat → Link
 output : Nat → Link

def Valid (q : Cursor) : Prop :=
 Writable q.memory q.owner q.token q.cell ∧
 q.cell.size=q.capacity*8 ∧ q.cell.alignment=2 ∧
 q.written≤q.read ∧ q.read≤q.length ∧ q.length≤q.capacity ∧
 (∀ i, q.read≤i → i<q.length → NativeView q.cell (i*8) (q.source i)) ∧
 (∀ i, i<q.written → NativeView q.cell (i*8) (q.output i))

/-- Reading advances before a possible destination write. No heap access is duplicated. -/
def advance (q : Cursor) : Cursor := {q with read:=q.read+1}

def sink (q : Cursor) (v : Link) : Cursor :=
 let c:=store q.cell (q.written*8) 8 (PV_OWNB_LinkBytes.encode v)
 {q with cell:=c,written:=q.written+1,
  memory:={q.memory with heap:=put q.memory.heap q.token.address (some c)},
  output:=fun i=>if i=q.written then v else q.output i}

attribute [local irreducible] Valid advance sink
end R1Z.PV_OWNB_Cursor
