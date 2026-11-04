import PV_B3P_PanicPatterns571227
namespace PV_B3P_MetadataSource580227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Local metadata/stack observations only; a slice records its fat-reference
length without assigning semantics to its element pointer or contents. -/
inductive Value where
  | scalar (n : Nat)
  | slice (length : Nat)
  | reference (slot : Nat)
  | pair (left right : Value)
  | boolean (b : Bool)
  | dead
abbrev Store := Nat → Value

def put (s : Store) (slot : Nat) (value : Value) : Store :=
  fun q => if q = slot then value else s q

def lengthValue : Value → Value
  | .slice n => .scalar n
  | _ => .dead

def load (s : Store) : Value → Value
  | .reference slot => s slot
  | _ => .dead

def field (second : Bool) : Value → Value
  | .pair a b => if second then b else a
  | _ => .dead

def equal : Value → Value → Value
  | .scalar a, .scalar b => .boolean (decide (a=b))
  | _, _ => .dead

def lessEqual (bound : Nat) : Value → Value
  | .scalar n => .boolean (decide (n≤bound))
  | _ => .dead

inductive Instr where
  | kill (slot : Nat)
  | copy (dest src : Nat)
  | lenCall (dest src : Nat)
  | address (dest src : Nat)
  | pairMove (dest left right : Nat)
  | field (dest src : Nat) (second : Bool)
  | load (dest src : Nat)
  | equalMove (dest left right : Nat)
  | leMove (dest src bound : Nat)

def step (i : Instr) (s : Store) : Store :=
  match i with
  | .kill slot => put s slot .dead
  | .copy dest src => put s dest (s src)
  | .lenCall dest src => put (put s src .dead) dest (lengthValue (s src))
  | .address dest src => put s dest (.reference src)
  | .pairMove dest left right => put (put (put s left .dead) right .dead) dest (.pair (s left) (s right))
  | .field dest src second => put s dest (field second (s src))
  | .load dest src => put s dest (load s (s src))
  | .equalMove dest left right => put (put (put s left .dead) right .dead) dest (equal (s left) (s right))
  | .leMove dest src bound => put (put s src .dead) dest (lessEqual bound (s src))

def run : List Instr → Store → Store
  | [], s => s
  | i::rest, s => run rest (step i s)

/-- Every statement of dot224's prefix, including the two slice::len calls,
stack addresses, tuple transfers, dereferences, and Move invalidations. -/
def equalityProgram : List Instr :=
  [.kill 0,.kill 3,.kill 4,.kill 5,.kill 6,.copy 6 1,.lenCall 5 6,.kill 6,
   .address 4 5,.kill 7,.kill 8,.kill 9,.copy 9 2,.lenCall 8 9,.kill 9,
   .address 7 8,.pairMove 3 4 7,.kill 7,.kill 4,.kill 10,.field 10 3 false,
   .kill 11,.field 11 3 true,.kill 12,.kill 13,.load 13 10,.kill 14,.load 14 11,
   .equalMove 12 13 14]

def equalityState (prior : Store) (left right : Nat) : Store :=
  run equalityProgram (put (put prior 1 (.slice left)) 2 (.slice right))

theorem equality_value (prior : Store) (n : Nat) : equalityState prior n n 12 = .boolean true := by
  simp only [equalityState,equalityProgram,run,step,put,lengthValue,field,load,equal,
    Nat.reduceEqDiff,Bool.false_eq_true,ite_true,ite_false,decide_true]

/-- Complete source prefix of qm31_pack_base4 up to its Le assertion.
The bound parameter is later fixed to the ACTUAL source constant4. -/
def packProgram (bound : Nat) : List Instr :=
  [.kill 0,.kill 2,.kill 3,.kill 4,.copy 4 1,.lenCall 3 4,.kill 4,.leMove 2 3 bound]

def packState (prior : Store) (length bound : Nat) : Store :=
  run (packProgram bound) (put prior 1 (.slice length))

theorem pack_value (prior : Store) (length slack : Nat) :
    packState prior length (length+slack) 2 = .boolean true := by
  simp only [packState,packProgram,run,step,put,lengthValue,lessEqual,
    Nat.reduceEqDiff,ite_true,ite_false]
  rw [decide_eq_true (Nat.le_add_right length slack)]

def condition (s : Store) (slot : Nat) : Bool :=
  match s slot with
  | .boolean b => b
  | _ => false

/-- The SAME interpreter retains the rejected cases; equal-size and <=4
certificates do not follow from an always-true condition evaluator. -/
theorem equality_rejects (prior : Store) (left right : Nat) (different : left ≠ right) :
    condition (equalityState prior left right) 12 = false := by
  simp only [condition,equalityState,equalityProgram,run,step,put,lengthValue,field,load,equal,
    Nat.reduceEqDiff,Bool.false_eq_true,ite_true,ite_false]
  rw [decide_eq_false different]

theorem pack_rejects (prior : Store) (length bound : Nat) (large : bound < length) :
    condition (packState prior length bound) 2 = false := by
  simp only [condition,packState,packProgram,run,step,put,lengthValue,lessEqual,
    Nat.reduceEqDiff,ite_true,ite_false]
  rw [decide_eq_false (by omega : ¬length≤bound)]

theorem equality_guard (prior : Store) (n : Nat) : condition (equalityState prior n n) 12 = true := by
  rw [condition,equality_value]

theorem pack_guard (prior : Store) (length slack : Nat) :
    condition (packState prior length (length+slack)) 2 = true := by
  rw [condition,pack_value]

theorem equality_certificate {α : Type} (prior : Store) (n : Nat) (normal first second : Result α) :
    ¬ diagnostic (condition (equalityState prior n n) 12 = true) ∧
      branch (condition (equalityState prior n n) 12 = true) normal first =
        branch (condition (equalityState prior n n) 12 = true) normal second :=
  (assertion _ true normal first second).2 (equality_guard prior n)

theorem pack_certificate {α : Type} (prior : Store) (length slack : Nat) (normal first second : Result α) :
    ¬ diagnostic (condition (packState prior length (length+slack)) 2 = true) ∧
      branch (condition (packState prior length (length+slack)) 2 = true) normal first =
        branch (condition (packState prior length (length+slack)) 2 = true) normal second :=
  (assertion _ true normal first second).2 (pack_guard prior length slack)
#print axioms equality_value
#print axioms pack_value
#print axioms equality_rejects
#print axioms pack_rejects
#print axioms equality_guard
#print axioms pack_guard
#print axioms equality_certificate
#print axioms pack_certificate
end PV_B3P_MetadataSource580227
