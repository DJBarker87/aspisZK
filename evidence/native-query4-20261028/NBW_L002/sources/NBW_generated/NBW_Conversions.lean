import NBO_Audit
set_option autoImplicit false
namespace NBW_Conversions
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- The frozen embedding canonicalizes its raw input; the cohort's literal
embedding is valid exactly on the canonical caller domain. -/
theorem base_canonical (m : U32) (hm : m.val<2147483647) :
 NBO_TailDomain.WideCanonical (NBF_RowInstall.embedM m) := by
 constructor
 · intro k
   fin_cases k <;> first | exact hm | decide
 · intro k
   fin_cases k <;> decide
/-- Native derived equality must compare all eight coordinates, not an
arbitrary selected limb. This is the exact structural cohort criterion. -/
theorem eq_coordinates (x y : Stage2E) : x=y ↔
 x.c0.c0.a=y.c0.c0.a ∧ x.c0.c0.b=y.c0.c0.b ∧
 x.c0.c1.a=y.c0.c1.a ∧ x.c0.c1.b=y.c0.c1.b ∧
 x.c1.c0.a=y.c1.c0.a ∧ x.c1.c0.b=y.c1.c0.b ∧
 x.c1.c1.a=y.c1.c1.a ∧ x.c1.c1.b=y.c1.c1.b := by
 constructor
 · intro h;subst y;exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 · rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
   rcases y with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,⟨⟨m,n⟩,⟨o,p⟩⟩⟩
   rintro ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
   rfl
#print axioms base_canonical
#print axioms eq_coordinates
end NBW_Conversions
