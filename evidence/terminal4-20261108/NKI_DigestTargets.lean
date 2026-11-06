import NKI_DigestView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_DigestTargets
open Aeneas Aeneas.Std Result
open NJX_DigestCohort (D dc dcells)
/-- Returned last-word target is the actual M31.add reply at this site. -/
structure Packet (d : D) (right : Bool) where
 last : U32
 call : if right then FIq_Native.field.M31.add (dcells d 7) NJX_AppendTargets.tweak=ok last else last=dcells d 7
 bound : last.val<2147483647
 value : last.val=NKI_DigestView.target d right 7

def cells {d : D} {right : Bool} (p : Packet d right) (i : Fin 8) : U32 :=
 if i=7 then p.last else dcells d i

theorem canonical {d : D} {right : Bool} (p : Packet d right) (hd : dc d) :
 ∀ i,(cells p i).val<2147483647 := by
 intro i
 unfold cells
 split
 · exact p.bound
 · exact hd _ (List.getElem_mem _)

theorem values {d : D} {right : Bool} (p : Packet d right) :
 ∀ i,(cells p i).val=NKI_DigestView.target d right i := by
 intro i
 by_cases h:i=7
 · subst i;exact p.value
 · simp only [cells,if_neg h,NKI_DigestView.target]
   have hn : i.val≠7 := by intro e;apply h;exact Fin.ext e
   simp only [hn,and_false,if_false]

#print axioms canonical
#print axioms values
end AspisR1.NKI_DigestTargets
end
