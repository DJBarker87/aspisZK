import NHI_FilledBridge
set_option autoImplicit false
namespace NHM_FilledFrame
open Aeneas Aeneas.Std Result AspisR1 NP6_StdModel

/-- The resize initialization invariant: a prefix is unchanged when one new
copy is appended, and the new selected cell is exactly the SAME input value. -/
theorem window {T : Type} (xs : List T) (value : T) (i : Nat) :
 (xs ++ [value])[i]? =
 if i < xs.length then xs[i]? else if i = xs.length then some value else none := by
 by_cases h : i < xs.length
 · simp [List.getElem?_append,h]
 · by_cases e : i=xs.length
   · subst i; simp
   · simp [List.getElem?_append,h]
     omega

/-- Induction on allocation initialization, with no successful-allocation premise. -/
theorem grow {T : Type} (n : Nat) (value : T) :
 List.replicate (n+1) value = List.replicate n value ++ [value] := by
 induction n with
 | zero => rfl
 | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons value) ih

#print axioms window
#print axioms grow
end NHM_FilledFrame
