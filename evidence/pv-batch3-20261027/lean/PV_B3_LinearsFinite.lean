import PV_B3_LinearsRank
import PV_B3_BoundedLoop
namespace PV_B3_LinearsFinite
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117 PV_B3_LinearsCounter
set_option autoImplicit false
 def body (point : Array Q 10#usize) (s : State) : Result (ControlFlow State (Q×Q)) :=
    host_arithmetic.selected_mask_linears_loop.body point s.1 s.2.1 s.2.2
 theorem decreases (point : Array Q 10#usize) (s t : State)
    (h : body point s = ok (cont t)) : PV_B3_LinearsRank.rank t < PV_B3_LinearsRank.rank s := by
  rcases s with ⟨a,b,i⟩
  exact PV_B3_LinearsRank.decreases point a b i t h
 theorem source (point : Array Q 10#usize) (a b : Q) (i : Usize) :
    host_arithmetic.selected_mask_linears_loop point a b i =
      PV_B3_BoundedLoop.bounded (body point) i.val (a,b,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body point) PV_B3_LinearsRank.rank
    (decreases point) i.val (a,b,i) (Nat.le_refl _)
#print axioms body
#print axioms decreases
#print axioms source
end PV_B3_LinearsFinite
