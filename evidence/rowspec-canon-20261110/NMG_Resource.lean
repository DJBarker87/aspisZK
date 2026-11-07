import Init
set_option autoImplicit false
namespace NMG_Resource
/-- Support carrier only. No claim that this interprets any frozen row. -/
structure Allocation where
 bytes : List UInt8
 capacity : Nat
 owner : Nat
 deriving DecidableEq
structure Heap where
 cells : Nat → Option Allocation
 next : Nat
/-- Existing owners and their complete initialized payload. -/
def WellFormed (h : Heap) : Prop :=
 ∀ id a, h.cells id=some a → id<h.next ∧ a.bytes.length≤a.capacity
inductive Action where
 | allocate (id : Nat) (a : Allocation)
 | write (id : Nat) (before after : Allocation)
 | transfer (id : Nat) (before after : Allocation)
 | free (id : Nat) (a : Allocation)
 deriving DecidableEq
/-- All writes have an exact old payload and exact new payload. -/
inductive Step : Heap → Action → Heap → Prop where
 | allocate (h : Heap) (a : Allocation) (capacity : a.bytes.length≤a.capacity)
   (fresh : h.cells h.next=none) :
   Step h (.allocate h.next a)
    ⟨fun id=>if id=h.next then some a else h.cells id,h.next+1⟩
 | write (h : Heap) (id : Nat) (a b : Allocation)
   (old : h.cells id=some a) (owner : b.owner=a.owner)
   (capacity : b.capacity=a.capacity) (extent : b.bytes.length=a.bytes.length) :
   Step h (.write id a b) ⟨fun k=>if k=id then some b else h.cells k,h.next⟩
 | transfer (h : Heap) (id : Nat) (a b : Allocation)
   (old : h.cells id=some a) (payload : b.bytes=a.bytes) (capacity : b.capacity=a.capacity) :
   Step h (.transfer id a b) ⟨fun k=>if k=id then some b else h.cells k,h.next⟩
 | free (h : Heap) (id : Nat) (a : Allocation) (old : h.cells id=some a) :
   Step h (.free id a) ⟨fun k=>if k=id then none else h.cells k,h.next⟩
inductive Trace : Heap → List Action → Heap → Prop where
 | nil (h : Heap) : Trace h [] h
 | cons {h m last : Heap} {e : Action} {es : List Action}
   (head : Step h e m) (tail : Trace m es last) : Trace h (e::es) last
/-- Terminal kind is distinct from the resource prefix at that terminal. -/
inductive Terminal (Reply Error : Type) where
 | returned (value : Reply)
 | error (error : Error)
 | abort
 | diverge
structure Observation (Reply Error : Type) where
 terminal : Terminal Reply Error
 after : Heap
 actions : List Action
end NMG_Resource
