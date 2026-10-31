import R1Z.PV_RDCD4_LazyComponents
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyPair
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents
/-- The two CM31 additions precede all component-channel additions, in source
order. In particular this is not components(left) then components(right). -/
def finish (q : Q) (sum : C) : Result (List (List M)) := do
  let c0 ← F.add q.c0.a q.c0.b
  let c1 ← F.add q.c1.a q.c1.b
  let c2 ← F.add sum.a sum.b
  ok [[q.c0.a,q.c0.b,c0],[q.c1.a,q.c1.b,c1],[sum.a,sum.b,c2]]
def pair (left right : Q) : Result (List (List M) × List (List M)) := do
  let leftSum ← F.cadd left.c0 left.c1
  let rightSum ← F.cadd right.c0 right.c1
  let l ← finish left leftSum
  let r ← finish right rightSum
  ok (l,r)
theorem order (left right : Q) : pair left right = (do
  let ls ← F.cadd left.c0 left.c1
  let rs ← F.cadd right.c0 right.c1
  let l ← finish left ls
  let r ← finish right rs
  ok (l,r)) := rfl
#print axioms order
end R1Z.PV_RDCD4_LazyPair
