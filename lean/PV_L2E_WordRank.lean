import PV_L2E_Dividend
set_option autoImplicit false
namespace PV_L2E_WordRank
open PV_L2D_DivisionBounds

/-- Input word lists follow the source's high-to-low division traversal. -/
def rank : List Nat → Nat
  | [] => 0
  | x::xs => x*B^xs.length+rank xs

theorem bound (xs : List Nat) (hx : ∀ x∈xs,x<B) : rank xs<B^xs.length := by
  induction xs with
  | nil => simp [rank]
  | cons x xs ih =>
    have h := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    have hb : 0<B^xs.length := pow_pos (by decide : 0<B) _
    simp only [rank,List.length_cons,pow_succ]
    nlinarith

/-- The complete quotient array and final remainder reconstruct the original
number, for every word count. No array contents are reduced by the kernel. -/
theorem reconstruct (r : Nat) (xs : List Nat) :
    rank (pass r xs).1*P+(pass r xs).2 = r*B^xs.length+rank xs := by
  induction xs generalizing r with
  | nil => simp [pass,rank]
  | cons x xs ih =>
    have h := ih (step r x).remainder
    have hd := step_reconstruct r x
    simp only [pass,rank,pass_length,List.length_cons,pow_succ]
    dsimp only [dividend] at hd
    nlinarith

#print axioms bound
#print axioms reconstruct
end PV_L2E_WordRank
