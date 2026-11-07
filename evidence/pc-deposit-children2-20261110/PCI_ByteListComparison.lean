import PCI_ByteComparison
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ByteListComparison

def compare (xy : U8 × U8) : Result Bool := do
 let b ← core.cmp.PartialEqU8.ne xy.1 xy.2
 ok (decide (¬ b=true))

theorem all (pairs : List (U8 × U8)) :
    List.allM compare pairs=ok (pairs.all (fun xy => decide (xy.1=xy.2))) := by
 induction pairs with
 | nil => rfl
 | cons pair rest ih =>
   cases pair with
   | mk x y =>
     by_cases h : x=y <;> simp [List.allM,compare,PCI_ByteComparison.ne,h,ih]
     all_goals rfl

theorem zipped (xs ys : List U8) (same : xs.length=ys.length) :
    (xs.zip ys).all (fun xy => decide (xy.1=xy.2))=decide (xs=ys) := by
 induction xs generalizing ys with
 | nil => cases ys <;> simp_all
 | cons x xs ih =>
   cases ys with
   | nil => simp_all
   | cons y ys =>
     have ht : xs.length=ys.length := by simpa using same
     simp only [List.zip_cons_cons,List.all_cons,ih ys ht,List.cons.injEq,Bool.decide_and]

#print axioms all
#print axioms zipped
end PCI_ByteListComparison
