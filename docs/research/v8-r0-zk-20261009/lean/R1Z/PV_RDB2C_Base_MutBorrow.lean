import R1Z.PV_RDB2C_Base_PointerBridge

/-! A handle restores into the CURRENT store, not a captured old snapshot.
This preserves writes from other live, disjoint mutable iterator borrows. -/
namespace R1Z.PV_RDB2_MutBorrow
set_option autoImplicit false

structure Cursor (T : Type) where
  cells : Nat → T
  front : Nat
  back : Nat
  length : Nat

structure Handle where
  index : Nat

def set {T : Type} (cells : Nat → T) (index : Nat) (value : T) : Nat → T :=
  fun i => if i = index then value else cells i

def restore {T : Type} (current : Cursor T) (handle : Handle) (value : T) : Cursor T :=
  {current with cells := set current.cells handle.index value}

def next {T : Type} (c : Cursor T) : Option (T × Handle × Cursor T) :=
  if c.front < c.back then some (c.cells c.front,⟨c.front⟩,{c with front := c.front+1})
  else none

def nextBack {T : Type} (c : Cursor T) : Option (T × Handle × Cursor T) :=
  if c.front < c.back then some (c.cells (c.back-1),⟨c.back-1⟩,{c with back := c.back-1})
  else none

theorem written {T : Type} (current : Cursor T) (h : Handle) (value : T) :
    (restore current h value).cells h.index = value := if_pos rfl

theorem frame {T : Type} (current : Cursor T) (h : Handle) (value : T) (i : Nat)
    (different : i ≠ h.index) :
    (restore current h value).cells i = current.cells i := if_neg different

theorem cursor_retained {T : Type} (current : Cursor T) (h : Handle) (value : T) :
    (restore current h value).front = current.front ∧
      (restore current h value).back = current.back ∧
      (restore current h value).length = current.length := ⟨rfl,rfl,rfl⟩

theorem forward_bounds {T : Type} (c : Cursor T) (active : c.front < c.back)
    (bounded : c.back ≤ c.length) : c.front < c.length ∧ c.front+1 ≤ c.back := by omega

theorem backward_bounds {T : Type} (c : Cursor T) (active : c.front < c.back)
    (bounded : c.back ≤ c.length) :
    0 < c.back ∧ c.front ≤ c.back-1 ∧ c.back-1 < c.length := by omega

#print axioms written
#print axioms frame
#print axioms cursor_retained
#print axioms forward_bounds
#print axioms backward_bounds
end R1Z.PV_RDB2_MutBorrow
