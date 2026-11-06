import NJH_BorrowModel
set_option autoImplicit false
namespace NJN_GuardModel
/-- Hand specification pending extraction; no native SDK interpretation asserted. -/
structure Cell where
  counter : Int
  length : Nat
  bytes : Nat → Nat
structure Account where
  cell : Nat
  metadata : Nat
structure Guard where
  cell : Nat
  exclusive : Bool
  deriving DecidableEq
structure Heap where
  accounts : Nat → Account
  cells : Nat → Cell
  tokens : Nat → Option Guard
  count : Nat

def replace {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

def acquire (h : Heap) (a token : Nat) (exclusive : Bool) : Heap × Except Unit Guard :=
  let cell := (h.accounts a).cell
  let n := (h.cells cell).counter
  let allowed := if exclusive then n = 0 else 0 ≤ n ∧ n < 9223372036854775807
  if allowed then
    let g := Guard.mk cell exclusive
    let c := { h.cells cell with counter := if exclusive then -1 else n+1 }
    ({h with cells := replace h.cells cell c, tokens := replace h.tokens token (some g)}, .ok g)
  else (h, .error ())

def deref (h : Heap) (g : Guard) : Cell := h.cells g.cell

def release (h : Heap) (token : Nat) (g : Guard) : Heap :=
  let c := h.cells g.cell
  let c' := { c with counter := if g.exclusive then c.counter+1 else c.counter-1 }
  { h with cells := replace h.cells g.cell c', tokens := replace h.tokens token none }

def write (h : Heap) (g : Guard) (i value : Nat) : Heap :=
  let c := h.cells g.cell
  {h with cells := replace h.cells g.cell {c with bytes := replace c.bytes i value}}

def Live (h : Heap) (token : Nat) (g : Guard) : Prop :=
  h.tokens token = some g ∧
  (if g.exclusive then (h.cells g.cell).counter = -1 else 0 < (h.cells g.cell).counter)

def Admitted (h : Heap) : Prop := h.count = 3 ∨ h.count = 7

/-- Cell replacement reads back the same cell, with no address-to-payload premise. -/
theorem selected {α : Type} (f : Nat → α) (i : Nat) (v : α) : replace f i v i = v := by
  simp [replace]
/-- Outside cells are unchanged. -/
theorem outside {α : Type} (f : Nat → α) (i j : Nat) (v : α) (hne : j ≠ i) :
    replace f i v j = f j := by simp [replace, hne]
#print axioms selected
#print axioms outside
end NJN_GuardModel
