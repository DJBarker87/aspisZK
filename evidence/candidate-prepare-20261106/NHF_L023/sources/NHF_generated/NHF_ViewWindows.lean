import NHF_ViewResult
set_option autoImplicit false
namespace AspisR1.NHF_ViewWindows
open Aeneas Aeneas.Std
abbrev E := AspisR1SelectedWideViewV1.aspis_core.field.wide_exact.WideExact
/-- Raw stored coordinates, without modular normalization. -/
def coordinate (x : E) (i : Fin 8) : U32 :=
 match i.val with
 | 0 => x.c0.c0.a
 | 1 => x.c0.c0.b
 | 2 => x.c0.c1.a
 | 3 => x.c0.c1.b
 | 4 => x.c1.c0.a
 | 5 => x.c1.c0.b
 | 6 => x.c1.c1.a
 | _ => x.c1.c1.b
/-- The eight native windows reconstruct the SAME record, not eight chosen
records or independently successful decoder runs. -/
theorem injective (x y : E) (same : ∀ i,coordinate x i=coordinate y i) : x=y := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rcases y with ⟨⟨⟨a',b'⟩,⟨c',d'⟩⟩,⟨⟨e',f'⟩,⟨g',h'⟩⟩⟩
 have h0:=same ⟨0,by decide⟩;change a=a' at h0
 have h1:=same ⟨1,by decide⟩;change b=b' at h1
 have h2:=same ⟨2,by decide⟩;change c=c' at h2
 have h3:=same ⟨3,by decide⟩;change d=d' at h3
 have h4:=same ⟨4,by decide⟩;change e=e' at h4
 have h5:=same ⟨5,by decide⟩;change f=f' at h5
 have h6:=same ⟨6,by decide⟩;change g=g' at h6
 have h7:=same ⟨7,by decide⟩;change h=h' at h7
 cases h0;cases h1;cases h2;cases h3;cases h4;cases h5;cases h6;cases h7;rfl
/-- Every byte input is either canonical at all eight words, or lies in one
of the eight rejecting windows. No canonical-input root restriction. -/
theorem domains_cover (words : Fin 8→Nat) :
 (∀ i,words i<2147483647) ∨ ∃ i,2147483647≤words i := by
 classical
 by_cases canonical:∀ i,words i<2147483647
 · exact Or.inl canonical
 · right
   push_neg at canonical
   exact canonical
/-- Tag and raw-coordinate windows suffice for the entire Option reply. -/
theorem option_ext (first second : Option E)
 (tag : first.isSome=second.isSome)
 (words : ∀ x y,first=some x→second=some y→∀ i,coordinate x i=coordinate y i) :
 first=second := by
 cases first with
 | none => cases second <;> simp_all
 | some x =>
   cases second with
   | none => cases tag
   | some y => exact congrArg some (injective x y (words x y rfl rfl))
#print axioms injective
#print axioms domains_cover
#print axioms option_ext
end AspisR1.NHF_ViewWindows
