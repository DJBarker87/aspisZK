import Aeneas.Std

/-! The finite readonly constant graph in the R440 monomorphic callback capture.
The captured x86_64 layout row for QM31 is size 16.  This file proves only the
explicit constant-fragment evaluation below; it is not an LLBC/Rust execution,
pointer-provenance, or fold correspondence theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R470R440ReadonlyConstantGraph
open Aeneas Aeneas.Std

inductive Value where
  | word (value : Usize)
  | bool (value : Bool)
  deriving DecidableEq

inductive Expr where
  | literal (value : Value)
  | sizeOf (typeId : Nat)
  | call (functionId : Nat)
  | global (globalId : Nat)
  | eq (left right : Expr)

-- R440: type2=QM31, layout size16; fun155=size_of, fun147=SIZE,
-- fun143=IS_ZST; global32=SIZE and global31=IS_ZST.
def targetLayoutSize (typeId : Nat) : Option Usize :=
  if typeId = 2 then some (16#usize) else none

def functionBody (id : Nat) : Option Expr :=
  if id = 155 then some (.sizeOf 2)
  else if id = 147 then some (.call 155)
  else if id = 143 then some (.eq (.global 32) (.literal (.word (0#usize))))
  else none

def globalInitializer (id : Nat) : Option Nat :=
  if id = 32 then some 147
  else if id = 31 then some 143
  else none

def valueEq : Value → Value → Option Value
  | .word left, .word right => some (.bool (decide (left = right)))
  | .bool left, .bool right => some (.bool (left == right))
  | _, _ => none

def eval : Nat → Expr → Option Value
  | 0, _ => none
  | fuel + 1, .literal value => some value
  | fuel + 1, .sizeOf typeId => (targetLayoutSize typeId).map Value.word
  | fuel + 1, .call functionId => (functionBody functionId).bind (eval fuel)
  | fuel + 1, .global globalId =>
      (globalInitializer globalId).bind (fun id => eval fuel (.call id))
  | fuel + 1, .eq left right => do
      let leftValue ← eval fuel left
      let rightValue ← eval fuel right
      valueEq leftValue rightValue

theorem sizeof_qm31 (fuel : Nat) :
    eval (fuel + 1) (.sizeOf 2) = some (.word (16#usize)) := by
  simp [eval, targetLayoutSize]

theorem size_global (fuel : Nat) :
    eval (fuel + 4) (.global 32) = some (.word (16#usize)) := by
  simp [eval, globalInitializer, functionBody, targetLayoutSize, Nat.add_assoc]

theorem is_zst_global (fuel : Nat) :
    eval (fuel + 7) (.global 31) = some (.bool false) := by
  simp [eval, globalInitializer, functionBody, targetLayoutSize, valueEq,
    Nat.add_assoc]

theorem is_zst_read_context {A : Type} (fuel : Nat)
    (continuation : Value → A) :
    (eval (fuel + 7) (.global 31)).map continuation =
      some (continuation (.bool false)) := by
  rw [is_zst_global]
  rfl

#print axioms targetLayoutSize
#print axioms functionBody
#print axioms globalInitializer
#print axioms valueEq
#print axioms eval
#print axioms sizeof_qm31
#print axioms size_global
#print axioms is_zst_global
#print axioms is_zst_read_context
end AspisV8R19.R470R440ReadonlyConstantGraph
