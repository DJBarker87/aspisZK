import PoolV_ChronologyStep
set_option autoImplicit false
namespace AspisR1.PoolV_ChronologySuffix
open Aeneas Aeneas.Std Result ControlFlow

def pairs (new old : Slice U64) (i : Nat) : List (U64 × U64) :=
  (new.val.drop i).zip (old.val.drop i)

def remaining (new old : Slice U64) (i : Nat) (d p : Bool) : Bool × Bool :=
  (d || (pairs new old i).any (fun x => decide (x.1 < x.2)),
   p || (pairs new old i).any (fun x => decide (x.1 > x.2)))

theorem cons_pairs (new old : Slice U64) (i : Nat)
    (hn : i < new.val.length) (ho : i < old.val.length) :
    pairs new old i = (new.val[i],old.val[i]) :: pairs new old (i+1) := by
  unfold pairs
  rw [List.drop_eq_getElem_cons hn,List.drop_eq_getElem_cons ho]
  rfl

theorem next (new old : Slice U64) (i : Nat) (d p : Bool)
    (hn : i < new.val.length) (ho : i < old.val.length) :
    remaining new old i d p = remaining new old (i+1)
      (d || decide (new.val[i] < old.val[i]))
      (p || decide (new.val[i] > old.val[i])) := by
  simp only [remaining,cons_pairs new old i hn ho,List.any_cons,Bool.or_assoc]

theorem end_new (new old : Slice U64) (i : Nat) (d p : Bool)
    (hn : new.val.length ≤ i) : remaining new old i d p = (d,p) := by
  simp [remaining,pairs,List.drop_eq_nil_of_le hn]

theorem end_old (new old : Slice U64) (i : Nat) (d p : Bool)
    (ho : old.val.length ≤ i) : remaining new old i d p = (d,p) := by
  simp [remaining,pairs,List.drop_eq_nil_of_le ho]

#print axioms cons_pairs
#print axioms next
#print axioms end_new
#print axioms end_old
end AspisR1.PoolV_ChronologySuffix
