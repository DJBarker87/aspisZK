import PV_EVH_VolatileClear
set_option autoImplicit false
namespace PV_EVH_HeapClear
open Aeneas Aeneas.Std PV_EVH_Runtime PV_EVH_HeapOwnership
open PV_EVH_VolatileClear
open PV_RJ4IDB (Bytes NativeEvent)

def sameKey (key : Key) (b : Block) : Bool :=
  b.identity == key.identity && b.owner == key.owner

/-- Lookup uses owner and identity; extensional contents never choose storage.
Invalid lookup or an oversized initialized prefix is an explicit runtime fault. -/
def clearOwned (encode : Event → Bytes) (key : Key) (initialized : Nat) : Q Unit := fun w =>
  match w.heap.find? (sameKey key) with
  | none => ⟨.fault (.invalidMemory key.identity),w,[]⟩
  | some b =>
    if initialized ≤ b.bytes.length then
      let updated := clearBlock b initialized
      ⟨.returned (.ok ()), {w with heap := w.heap.map
        (fun old => if sameKey key old then updated else old)},
        (stores key 0 initialized ++ [.fence]).map
          (fun e => .side [122,101,114,111,105,122,101] (encode e))⟩
    else ⟨.fault (.invalidMemory key.identity),w,[]⟩

theorem missing_owner_fault (encode : Event → Bytes) (key : Key) (n : Nat) (w : State)
    (h : w.heap.find? (sameKey key) = none) :
    clearOwned encode key n w = ⟨.fault (.invalidMemory key.identity),w,[]⟩ := by
  simp only [clearOwned,h]

theorem invalid_prefix_fault (encode : Event → Bytes) (key : Key) (n : Nat)
    (w : State) (b : Block) (hb : w.heap.find? (sameKey key) = some b)
    (h : ¬ n ≤ b.bytes.length) :
    clearOwned encode key n w = ⟨.fault (.invalidMemory key.identity),w,[]⟩ := by
  simp only [clearOwned,hb,h,if_false]

theorem successful_clear (encode : Event → Bytes) (key : Key) (n : Nat)
    (w : State) (b : Block) (hb : w.heap.find? (sameKey key) = some b)
    (h : n ≤ b.bytes.length) :
    (clearOwned encode key n w).outcome = .returned (.ok ()) ∧
    (clearOwned encode key n w).state.heap = w.heap.map
      (fun old => if sameKey key old then clearBlock b n else old) ∧
    (clearOwned encode key n w).state.allocator = w.allocator ∧
    (clearOwned encode key n w).state.errno = w.errno ∧
    (clearOwned encode key n w).events = (stores key 0 n ++ [.fence]).map
      (fun e => .side [122,101,114,111,105,122,101] (encode e)) := by
  simp only [clearOwned,hb,h,if_true,and_self]

/-- Every unrelated allocation stays byte-for-byte unchanged in the heap map. -/
theorem other_allocation_unchanged (key : Key) (b c : Block) (n : Nat)
    (h : sameKey key c = false) :
    (if sameKey key c then clearBlock b n else c) = c := by
  simp only [h,Bool.false_eq_true,if_false]

theorem cleared_owner_view (heap : List Block) (v : View) (b : Block)
    (h : Owns heap v b) :
    let cleared := clearBlock b v.contents.length
    Owns [cleared] ⟨v.key,List.replicate v.contents.length 0,v.capacity⟩ cleared := by
  have hlen : v.contents.length ≤ b.bytes.length := by
    rw [h.2.2.2.2.1]
    exact h.2.2.2.2.2.1
  exact ⟨List.mem_cons_self,h.2.1,h.2.2.1,h.2.2.2.1,
    (clear_length b v.contents.length hlen).trans h.2.2.2.2.1,
    by simpa only [List.length_replicate] using h.2.2.2.2.2.1,
    by simpa only [List.length_replicate] using clear_initialized b v.contents.length⟩

#print axioms missing_owner_fault
#print axioms invalid_prefix_fault
#print axioms successful_clear
#print axioms other_allocation_unchanged
#print axioms cleared_owner_view
end PV_EVH_HeapClear
