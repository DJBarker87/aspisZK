import NLQ_Stage1Guard
set_option autoImplicit false
namespace NMB_Guard
open Aeneas Aeneas.Std AspisR1
/-- The same frozen guard is used by stage1 and stage1_owned. -/
def reject (data : List U8) (count : Nat) : Bool :=
 !(decide (data=[3#u8,10#u8]) || decide (data=[3#u8,11#u8])) || decide (count≠3)
def reference (data : List U8) (count : Nat) : Bool :=
 match data with
 | [a,b] => !(decide (a=3#u8) && (decide (b=10#u8) || decide (b=11#u8)) && decide (count=3))
 | _ => true
theorem source (data : List U8) (count : Nat) : reject data count=reference data count := by
 cases data with
 | nil => simp [reject,reference]
 | cons a rest =>
  cases rest with
  | nil => simp [reject,reference]
  | cons b rest =>
   cases rest with
   | nil =>
    by_cases ha : a=3#u8 <;> by_cases hb : b=10#u8 <;>
     by_cases hc : b=11#u8 <;> by_cases hn : count=3 <;>
     simp_all [reject,reference]
   | cons c rest => simp [reject,reference]
theorem accepted (data : List U8) (count : Nat) : reject data count=false ↔
 (data=[3#u8,10#u8] ∨ data=[3#u8,11#u8]) ∧ count=3 := by
 by_cases ten : data=[3#u8,10#u8] <;>
  by_cases eleven : data=[3#u8,11#u8] <;> by_cases n : count=3 <;>
  simp_all [reject]
#print source
#print accepted
#print axioms source
#print axioms accepted
end NMB_Guard
