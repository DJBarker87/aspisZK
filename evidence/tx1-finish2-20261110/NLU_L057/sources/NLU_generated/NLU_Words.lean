import NLU_State
set_option autoImplicit false
namespace AspisR1.NLU
open Aeneas Aeneas.Std AspisR1PublicPreparation
abbrev Q := aspis_core.field.QM31
def word (q : Q) (i : Fin 4) : U32 :=
 if i.val=0 then q.c0.a else if i.val=1 then q.c0.b else if i.val=2 then q.c1.a else q.c1.b
/-- Reassemble four universally quantified native scalar windows. No field
arithmetic or large numeral normalization is involved. -/
theorem word_ext (a b : Q) (same : ∀ i,word a i=word b i) : a=b := by
 have h0:=same ⟨0,by decide⟩
 have h1:=same ⟨1,by decide⟩
 have h2:=same ⟨2,by decide⟩
 have h3:=same ⟨3,by decide⟩
 simp only [word,ite_true,ite_false,show (0:Nat)≠1 by decide,show (1:Nat)≠0 by decide,
  show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,show (3:Nat)≠0 by decide,
  show (3:Nat)≠1 by decide,show (3:Nat)≠2 by decide] at h0 h1 h2 h3
 cases a with
 | mk a0 a1 =>
   cases b with
   | mk b0 b1 =>
     cases a0
     cases a1
     cases b0
     cases b1
     cases h0;cases h1;cases h2;cases h3;rfl
#print axioms word_ext
end AspisR1.NLU
