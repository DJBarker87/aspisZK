import PV_EVH_EntropyCleanup
set_option autoImplicit false
namespace PV_EVH_ZeroizeArray
open Aeneas Aeneas.Std PV_EVH_Runtime PV_EVH_HeapOwnership
open PV_EVH_VolatileClear (clearBlock)
open PV_RJ4IDB (Bytes NativeEvent)

/-- zeroize 1.9.0's u8 scalar implementation writes default zero and calls
optimization_barrier for EACH element. This is not volatile_clear's final fence. -/
inductive Event where
  | store (key : Key) (offset : Nat)
  | barrier (key : Key) (offset : Nat)
  deriving DecidableEq

def events (key : Key) (offset : Nat) : Nat → List Event
  | 0 => []
  | n+1 => .store key offset :: .barrier key offset :: events key (offset+1) n

def cells (key : Key) (offset : Nat) : Bytes → Bytes × List Event
  | [] => ([],[])
  | _ :: rest =>
    let next := cells key (offset+1) rest
    (0 :: next.1, .store key offset :: .barrier key offset :: next.2)

theorem cells_exact (key : Key) (offset : Nat) (values : Bytes) :
    cells key offset values = (List.replicate values.length 0, events key offset values.length) := by
  induction values generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    simp only [cells,ih,List.length_cons,List.replicate_succ,events]

/-- Memory identity and stack/native address association remain explicit P work.
In particular this generic owner-indexed operation alone cannot install a Rust
stack array into the allocator-only State.heap. -/
def zeroizeOwned (encode : Event → Bytes) (key : Key) (initialized : Nat) : Q Unit := fun w =>
  match w.heap.find? (PV_EVH_HeapClear.sameKey key) with
  | none => ⟨.fault (.invalidMemory key.identity),w,[]⟩
  | some b =>
    if initialized ≤ b.bytes.length then
      let post : State := {w with heap := (w.heap.map
        (fun old => if PV_EVH_HeapClear.sameKey key old then clearBlock b initialized else old))}
      ⟨.returned (.ok ()),post,(events key 0 initialized).map
        (fun e => .side [122,101,114,111,105,122,101] (encode e))⟩
    else ⟨.fault (.invalidMemory key.identity),w,[]⟩

theorem zeroize_sequence (encode : Event → Bytes) (key : Key) (n : Nat)
    (w : State) (b : Block)
    (hb : w.heap.find? (PV_EVH_HeapClear.sameKey key) = some b)
    (hn : n ≤ b.bytes.length) :
    (zeroizeOwned encode key n w).events = (events key 0 n).map
      (fun e => .side [122,101,114,111,105,122,101] (encode e)) ∧
    (zeroizeOwned encode key n w).outcome = .returned (.ok ()) := by
  simp only [zeroizeOwned,hb,hn,if_true,and_self]

/-- Ordinary fill errors use the same original key and clear all 64 initialized
bytes, even when the OS changed only a prefix. Native stack association OPEN. -/
def entropyFill {E B : Type} (encode : Event → Bytes) (key : Key)
    (fill : Q (core.result.Result Unit E)) (consume : Q (core.result.Result B E)) :
    Q (core.result.Result B E) :=
  PV_EVH_EntropyCleanup.fillScope fill consume (zeroizeOwned encode key 64)

theorem entropy_error_cleanup {E B : Type} (encode : Event → Bytes) (key : Key)
    (fill : Q (core.result.Result Unit E)) (consume : Q (core.result.Result B E))
    (w : State) (e : E) (h : (fill w).outcome = .returned (.ok (.Err e))) :
    entropyFill encode key fill consume w =
      let cleaned := PV_EVH_Runtime.bind (zeroizeOwned encode key 64)
        (fun _ => PV_EVH_Runtime.lift (.ok (core.result.Result.Err (T := B) e))) (fill w).state
      ⟨cleaned.outcome,cleaned.state,(fill w).events ++ cleaned.events⟩ :=
  PV_EVH_EntropyCleanup.error_cleanup_world fill consume _ w e h

#print axioms cells_exact
#print axioms zeroize_sequence
#print axioms entropy_error_cleanup
end PV_EVH_ZeroizeArray
