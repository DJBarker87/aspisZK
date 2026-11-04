import NFT_Karatsuba
import ExtractedMaskQM31Exact
import ExtractedMaskQM31SquareExact
set_option autoImplicit false
namespace NGA_SquareCallees
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Q := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem product (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 ∃ z, field.QM31.mul x y=ok z ∧ Canonical z ∧ decode z=decode x*decode y :=
 AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact x y hx hy

theorem square (x : Q) (hx : Canonical x) :
 ∃ z, field.QM31.square x=ok z ∧ Canonical z ∧ decode z=decode x*decode x :=
 AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact x hx

theorem addition (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 ∃ z, field.QM31.add x y=ok z ∧ Canonical z ∧ decode z=decode x+decode y :=
 AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact x y hx hy

/-- Exact source mul_u cut on the same coherent QM31 carrier. -/
def mulU (x : Q) : Result Q := do
 let r ← field.mul_by_r x.c1
 ok ⟨r,x.c0⟩

theorem mulU_words (x : Q) (hx : Canonical x) :
 ∃ z, mulU x=ok z ∧ Canonical z ∧
   z.c0.a.val=(((x.c1.a.val+x.c1.a.val)%2147483647)+2147483647-x.c1.b.val)%2147483647 ∧
   z.c0.b.val=(x.c1.a.val+((x.c1.b.val+x.c1.b.val)%2147483647))%2147483647 ∧ z.c1=x.c0 := by
 obtain ⟨r,hr,hc,ha,hb⟩ := NFT_Karatsuba.mul_r_value x.c1 hx.2
 exact ⟨⟨r,x.c0⟩,by simp only [mulU,hr,bind_tc_ok],⟨hc,hx.1⟩,ha,hb,rfl⟩

#print axioms product
#print axioms square
#print axioms addition
#print axioms mulU_words
end NGA_SquareCallees
