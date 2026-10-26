import NP6_ClaimsRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsExt
open Aeneas Aeneas.Std AspisR1ClaimsUnrolledParent

def limb (q : aspis_core.field.QM31) (i : Fin 4) : Nat :=
  if i.val=0 then q.c0.a.val else if i.val=1 then q.c0.b.val
  else if i.val=2 then q.c1.a.val else q.c1.b.val

theorem qm_ext (q r : aspis_core.field.QM31)
    (same : ∀ i, limb q i = limb r i) : q = r := by
  have h0 : q.c0.a=r.c0.a := UScalar.eq_of_val_eq (by simpa [limb] using same ⟨0,by decide⟩)
  have h1 : q.c0.b=r.c0.b := UScalar.eq_of_val_eq (by simpa [limb] using same ⟨1,by decide⟩)
  have h2 : q.c1.a=r.c1.a := UScalar.eq_of_val_eq (by simpa [limb] using same ⟨2,by decide⟩)
  have h3 : q.c1.b=r.c1.b := UScalar.eq_of_val_eq (by simpa [limb] using same ⟨3,by decide⟩)
  cases q with
  | mk a b =>
    cases r with
    | mk c d =>
      cases a; cases b; cases c; cases d
      simp_all only [aspis_core.field.CM31.mk.injEq,aspis_core.field.QM31.mk.injEq]

def cell (out : Claims) (p : Fin 3) (j : Fin 29) : aspis_core.field.QM31 :=
  let row := out.val[p.val]'(by simpa only [out.property] using p.isLt)
  row.val[j.val]'(by simpa only [row.property] using j.isLt)

/-- Scalar projection is injective on the full selected Claims carrier,
including all three rows and all four native u32 limbs. -/
theorem claims_ext (a b : Claims)
    (same : ∀ p j i, limb (cell a p j) i = limb (cell b p j) i) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro p pa pb
    apply Subtype.ext
    apply List.ext_getElem
    · exact (a.val[p]).property.trans (b.val[p]).property.symm
    · intro j ja jb
      apply qm_ext
      intro i
      have hp : p<3 := by simpa only [a.property] using pa
      have hj : j<29 := by simpa only [(a.val[p]).property] using ja
      exact same ⟨p,hp⟩ ⟨j,hj⟩ i

#print axioms qm_ext
#print axioms claims_ext
end AspisR1.NP6_ClaimsExt
end
