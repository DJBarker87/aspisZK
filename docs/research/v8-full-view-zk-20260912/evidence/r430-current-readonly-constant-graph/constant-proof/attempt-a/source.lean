import Aeneas.Std

/-! The readonly constant graph captured in R429, interpreted with the explicit
size-of primitive rule: a size-of call returns the captured target layout size.
This is a constant-fragment model, not a Rust heap/pointer semantics or whole
fold execution theorem. The source-to-fragment checks and the primitive trust
boundary must be retained when using this result for a translator change. -/
set_option autoImplicit false
namespace AspisV8R19.R430ReadonlyConstantGraph
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

-- Exact selected target/type entry; this does not infer a layout for another ABI.
def targetLayoutSize (typeId : Nat) : Option Usize :=
  if typeId = 2 then some (16#usize) else none

-- Function153: intrinsic size_of::<QM31>; function145: SIZE initializer;
-- function142: IS_ZST initializer. Global31/32 refer to those initializers.
def functionBody (id : Nat) : Option Expr :=
  if id = 153 then some (.sizeOf 2)
  else if id = 145 then some (.call 153)
  else if id = 142 then some (.eq (.global 32) (.literal (.word (0#usize))))
  else none

def globalInitializer (id : Nat) : Option Nat :=
  if id = 32 then some 145
  else if id = 31 then some 142
  else none

def valueEq : Value → Value → Option Value
  | .word left, .word right => some (.bool (decide (left = right)))
  | .bool left, .bool right => some (.bool (left == right))
  | _, _ => none

-- None is an unsupported/incomplete constant-fragment diagnostic, not a new
-- Rust runtime error. Fuel is used only to make this finite graph evaluator total.
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

theorem size_initializer (fuel : Nat) :
    eval (fuel + 3) (.call 145) = some (.word (16#usize)) := by
  simp [eval, functionBody, targetLayoutSize, Nat.add_assoc]

theorem size_global (fuel : Nat) :
    eval (fuel + 4) (.global 32) = some (.word (16#usize)) := by
  simp [eval, globalInitializer, functionBody, targetLayoutSize, Nat.add_assoc]

theorem is_zst_initializer (fuel : Nat) :
    eval (fuel + 6) (.call 142) = some (.bool false) := by
  simp [eval, globalInitializer, functionBody, targetLayoutSize, valueEq,
    Nat.add_assoc]

theorem is_zst_global (fuel : Nat) :
    eval (fuel + 7) (.global 31) = some (.bool false) := by
  simp [eval, globalInitializer, functionBody, targetLayoutSize, valueEq,
    Nat.add_assoc]

-- The selected scalar reads can be replaced by their literal values in any
-- caller continuation. Equality here preserves all caller failures/divergence
-- and any caller-managed state; no assumptions on the continuation are used.
theorem size_read_context {A : Type} (fuel : Nat)
    (continuation : Value → A) :
    (eval (fuel + 4) (.global 32)).map continuation =
      some (continuation (.word (16#usize))) := by
  rw [size_global]
  rfl

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
#print axioms size_initializer
#print axioms size_global
#print axioms is_zst_initializer
#print axioms is_zst_global
#print axioms size_read_context
#print axioms is_zst_read_context
end AspisV8R19.R430ReadonlyConstantGraph
