import NCJ_WordIdentity
set_option autoImplicit false
namespace NDL_WideWords
open Aeneas Aeneas.Std AspisR1 LPi_FieldValues

def word (x : NE) (i : Nat) : Nat := match i with
  | 0 => x.c0.c0.a.val | 1 => x.c0.c0.b.val
  | 2 => x.c0.c1.a.val | 3 => x.c0.c1.b.val
  | 4 => x.c1.c0.a.val | 5 => x.c1.c0.b.val
  | 6 => x.c1.c1.a.val | _ => x.c1.c1.b.val

/-- One arbitrary word observation composes to the COMPLETE typed E carrier;
no independently selected coordinates or equality oracle is introduced. -/
theorem injective (x y : NE) (same : ∀ i,i<8 → word x i=word y i) : x=y := by
  apply NCJ_WordIdentity.wide
  exact Prod.ext
    (Prod.ext (Prod.ext (same 0 (by decide)) (same 1 (by decide)))
      (Prod.ext (same 2 (by decide)) (same 3 (by decide))))
    (Prod.ext (Prod.ext (same 4 (by decide)) (same 5 (by decide)))
      (Prod.ext (same 6 (by decide)) (same 7 (by decide))))

#print axioms injective
end NDL_WideWords
