import NKJ_Scalar
import NGA_ArrayExt
set_option autoImplicit false
namespace NKJ_NativeStep
open Aeneas Aeneas.Std Result NGA_Cell

/-- Typed composition of source cuts S,P,A,W. The native certificates select the
same two words, evaluate the raw product, check +=, then write this selected cell.
The full complement frame is part of W; no independent reply is quantified. -/
def run (s : Sums) (l r : Cache) (c : Cell) : Result Sums := do
 let value ← NKJ_Scalar.update (get s c) (get l c) (get r c)
 ok (set s c value)

theorem source (s : Sums) (l r : Cache) (c : Cell)
 (hl : (get l c).val<2147483647) (hr : (get r c).val<2147483647)
 (hs : (get s c).val≤3*(2147483647-1)^2) :
 run s l r c=step s l r (uFin c.1) (uFin c.2) := by
 obtain ⟨v,hv,vv,_⟩ := NKJ_Scalar.update_value (get s c) (get l c) (get r c) hl hr hs
 obtain ⟨out,ho,vo⟩ := NGA_Step.source s l r c hl hr hs
 have same : set s c v=out := by
  apply NGA_ArrayExt.source
  intro d
  rw [get_set,vo d]
  by_cases h : d=c
  · subst d;simp only [if_pos rfl];exact vv
  · simp only [if_neg h,Nat.add_zero]
 simp only [run,hv,bind_tc_ok,ho,same]
#print axioms source
end NKJ_NativeStep
