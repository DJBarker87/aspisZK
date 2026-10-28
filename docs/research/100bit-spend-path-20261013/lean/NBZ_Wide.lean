import NBW_Audit
import ExtractedMaskBasisComponents
set_option autoImplicit false
noncomputable section
namespace NBZ_Wide
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NBO_FieldPorts
open NBO_TailDomain (WideCanonical)
abbrev CanonQ := ExtractedMaskQM31Exact.CurrentCanonicalQM
private theorem qadd (x y : NQ) (hx : CanonQ x) (hy : CanonQ y) :
 ∃ z, AspisR1SelectedMaskProbe.field.QM31.add x y=ok z ∧ CanonQ z := by
 obtain ⟨z,hz,cz,_⟩ := ExtractedMaskQM31Exact.current_qm_add_exact x y hx hy
 exact ⟨z,hz,cz⟩
private theorem qmul (x y : NQ) (hx : CanonQ x) (hy : CanonQ y) :
 ∃ z, AspisR1SelectedMaskProbe.field.QM31.mul x y=ok z ∧ CanonQ z := by
 obtain ⟨z,hz,cz,_⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact x y hx hy
 exact ⟨z,hz,cz⟩
def u (x : NQ) : Result NQ := do
 let r ← AspisR1SelectedMaskProbe.field.mul_by_r x.c1
 ok ⟨r,x.c0⟩
/-- Reuse the retained CM basis law; no new field arithmetic proof. -/
theorem u_total (x : NQ) (hx : CanonQ x) :
 ∃ z, u x=ok z ∧ CanonQ z := by
 obtain ⟨r,hr,cr,_⟩ := ExtractedMaskBasisComponents.current_cm31_mul_r_words x.c1 hx.2
 rw [ExtractedMaskBasisComponents.cm31_mul_r_eq_mul_by_r] at hr
 exact ⟨⟨r,x.c0⟩,by simp only [u,hr,bind_tc_ok],⟨cr,hx.1⟩⟩
/-- Literal Karatsuba operation order of the retained WideExact product,
transported to the coherent SelectedMask carrier. Native binding is NBC_FieldOps. -/
def product (x y : Stage2E) : Result Stage2E := do
 let ac ← AspisR1SelectedMaskProbe.field.QM31.mul (toQ x.c0) (toQ y.c0)
 let bd ← AspisR1SelectedMaskProbe.field.QM31.mul (toQ x.c1) (toQ y.c1)
 let xs ← AspisR1SelectedMaskProbe.field.QM31.add (toQ x.c0) (toQ x.c1)
 let ys ← AspisR1SelectedMaskProbe.field.QM31.add (toQ y.c0) (toQ y.c1)
 let cross ← AspisR1SelectedMaskProbe.field.QM31.mul xs ys
 let ub ← u bd
 let lo ← AspisR1SelectedMaskProbe.field.QM31.add ac ub
 let hi0 ← NBO_FoldLinear.qsub cross ac
 let hi ← NBO_FoldLinear.qsub hi0 bd
 ok (fromE (lo,hi))
/-- Every internal field domain is derived from the preceding concrete return. -/
theorem product_total (x y : Stage2E) (hx : WideCanonical x) (hy : WideCanonical y) :
 ∃ z, product x y=ok z ∧ WideCanonical z := by
 have cx := (canonicalE x).mp hx
 have cy := (canonicalE y).mp hy
 obtain ⟨ac,hac,cac⟩ := qmul (toQ x.c0) (toQ y.c0) cx.1 cy.1
 obtain ⟨bd,hbd,cbd⟩ := qmul (toQ x.c1) (toQ y.c1) cx.2 cy.2
 obtain ⟨xs,hxs,cxs⟩ := qadd (toQ x.c0) (toQ x.c1) cx.1 cx.2
 obtain ⟨ys,hys,cys⟩ := qadd (toQ y.c0) (toQ y.c1) cy.1 cy.2
 obtain ⟨cross,hcross,ccross⟩ := qmul xs ys cxs cys
 obtain ⟨ub,hub,cub⟩ := u_total bd cbd
 obtain ⟨lo,hlo,clo⟩ := qadd ac ub cac cub
 obtain ⟨hi0,hhi0,chi0⟩ := NBO_FoldLinear.qsub_total cross ac ccross cac
 obtain ⟨hi,hhi,chi⟩ := NBO_FoldLinear.qsub_total hi0 bd chi0 cbd
 exact ⟨fromE (lo,hi),by simp only [product,hac,hbd,hxs,hys,hcross,hub,hlo,hhi0,hhi,bind_tc_ok],
   fromE_canonical _ ⟨clo,chi⟩⟩
/-- Discharge the inherited generic Horner totality law for this concrete
probe operation. This is a domain theorem, not a native fold bridge. -/
theorem horner_total (alpha tail : Stage2E) (ha : WideCanonical alpha)
 (ht : WideCanonical tail) (coefficients : List Stage2E)
 (hc : ∀ h ∈ coefficients, WideCanonical h) :
 ∃ z, NBW_Horner.eval product alpha coefficients tail=ok z ∧ WideCanonical z :=
 NBW_Horner.total product product_total alpha tail ha ht coefficients hc
#print axioms qadd
#print axioms qmul
#print axioms u_total
#print axioms product_total
#print axioms horner_total
end NBZ_Wide
end
