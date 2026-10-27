import PV_B3_LinearsGuard
namespace PV_B3_LinearsRank
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117 PV_B3_LinearsCounter
set_option autoImplicit false
 theorem decrement (i : Usize) (h : 0 < i.val) :
    (Usize.wrapping_sub i 1#usize).val = i.val-1 := by
  change (i.bv-(1#usize).bv).toNat = i.val-1
  exact BitVec.toNat_sub_of_le (by simpa using h)
 def rank (s : State) : Nat := s.2.2.val
 theorem decreases (point : Array Q 10#usize) (a b : Q) (i : Usize) (next : State)
    (h : host_arithmetic.selected_mask_linears_loop.body point a b i = ok (cont next)) :
    rank next < rank (a,b,i) := by
  obtain ⟨hi,hn⟩ := PV_B3_LinearsGuard.continued point a b i next h
  unfold rank
  dsimp only
  rw [hn,decrement i hi]
  omega
#print axioms decrement
#print axioms rank
#print axioms decreases
end PV_B3_LinearsRank
