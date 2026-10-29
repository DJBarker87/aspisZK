import R1Z.PV_OWNC_InPlaceResult
set_option autoImplicit false
namespace R1Z.PV_OWNC_Vector
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View
/-- Initialized-prefix carrier used after in-place collection and before each
Vec::push. A single byte cell is authoritative; spare cells stay unconstrained. -/
structure Buffer (T : Type) where
 memory : Memory
 token : Token
 owner : Nat
 cell : Cell
 length : Nat
 capacity : Nat
 values : Nat → T

def View {T : Type} (k : Codec T) (c : Cell) (s : Nat) (v : T) : Prop :=
 PV_OWNB_PaddingStore.Represents (k.encode v) k.width c s

def Valid {T : Type} (k : Codec T) (b : Buffer T) : Prop :=
 Writable b.memory b.owner b.token b.cell ∧ b.cell.size=b.capacity*k.width ∧
 b.cell.alignment=k.alignment ∧ b.length≤b.capacity ∧
 ∀ i, i<b.length → View k b.cell (i*k.width) (b.values i)

def push {T : Type} (k : Codec T) (b : Buffer T) (v : T) (actual : Bytes) : Buffer T :=
 let c:=store b.cell (b.length*k.width) k.width actual
 {b with
  cell:=c
  length:=b.length+1
  values:=fun i=>if i=b.length then v else b.values i
  memory:={b.memory with heap:=put b.memory.heap b.token.address (some c)}}
attribute [local irreducible] Valid View push
end R1Z.PV_OWNC_Vector
