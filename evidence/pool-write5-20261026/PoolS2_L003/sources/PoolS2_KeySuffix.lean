import PoolS2_KeyStep
set_option autoImplicit false
namespace AspisR1.PoolS2_KeySuffix
open Aeneas Aeneas.Std Result ControlFlow

def pairs (a b : Slice U8) (i : Nat) : List (U8 × U8) :=
  (a.val.drop i).zip (b.val.drop i)

def remaining (a b : Slice U8) (i : Nat) (equal : Bool) : Bool :=
  equal && (pairs a b i).all (fun p => decide (p.1 = p.2))

theorem cons_pairs (a b : Slice U8) (i : Nat)
    (ha : i < a.val.length) (hb : i < b.val.length) :
    pairs a b i = (a.val[i],b.val[i]) :: pairs a b (i+1) := by
  unfold pairs
  rw [List.drop_eq_getElem_cons ha,List.drop_eq_getElem_cons hb]
  rfl

theorem next (a b : Slice U8) (i : Nat) (equal : Bool)
    (ha : i < a.val.length) (hb : i < b.val.length) :
    remaining a b i equal = remaining a b (i+1) (equal && decide (a.val[i] = b.val[i])) := by
  simp only [remaining,cons_pairs a b i ha hb,List.all_cons,Bool.and_assoc]

theorem ended (a b : Slice U8) (i : Nat) (equal : Bool)
    (ha : a.val.length ≤ i) : remaining a b i equal = equal := by
  simp [remaining,pairs,List.drop_eq_nil_of_le ha]

#print axioms cons_pairs
#print axioms next
#print axioms ended
end AspisR1.PoolS2_KeySuffix
