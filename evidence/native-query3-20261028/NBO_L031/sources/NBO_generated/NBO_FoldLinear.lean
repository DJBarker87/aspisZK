import NBO_ProducerDomains
import ExtractedMaskScalarMul
set_option autoImplicit false
noncomputable section
namespace NBO_FoldLinear
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NBO_FieldPorts
open NBO_TailDomain (WideCanonical)
open NBO_FieldSemantics (add)
def qsub (x y : NQ) : Result NQ := do
 let a ← AspisR1SelectedMaskProbe.field.CM31.sub x.c0 y.c0
 let b ← AspisR1SelectedMaskProbe.field.CM31.sub x.c1 y.c1
 ok ⟨a,b⟩
def sub (x y : Stage2E) : Result Stage2E := do
 let a ← qsub (toQ x.c0) (toQ y.c0)
 let b ← qsub (toQ x.c1) (toQ y.c1)
 ok (fromE (a,b))
def scale (x : Stage2E) (s : U32) : Result Stage2E := do
 let a ← AspisR1SelectedMaskProbe.field.QM31.mul_m31 (toQ x.c0) s
 let b ← AspisR1SelectedMaskProbe.field.QM31.mul_m31 (toQ x.c1) s
 ok (fromE (a,b))
/-- Two retained CM results compose the actual probe QM subtraction body. -/
theorem qsub_total (x y : NQ)
 (hx : ExtractedMaskQM31Exact.CurrentCanonicalQM x)
 (hy : ExtractedMaskQM31Exact.CurrentCanonicalQM y) :
 ∃ z, qsub x y=ok z ∧
 ExtractedMaskQM31Exact.CurrentCanonicalQM z := by
 obtain ⟨a,ha,ca,_,_⟩ := ExtractedMaskTowerAdd.current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
 obtain ⟨b,hb,cb,_,_⟩ := ExtractedMaskTowerAdd.current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
 exact ⟨⟨a,b⟩,by simp only [qsub,ha,hb,bind_tc_ok],⟨ca,cb⟩⟩
theorem sub_total (x y : Stage2E) (hx : WideCanonical x) (hy : WideCanonical y) :
 ∃ z, sub x y=ok z ∧ WideCanonical z := by
 obtain ⟨a,ha,ca⟩ := qsub_total (toQ x.c0) (toQ y.c0) ((canonicalQ _).mp hx.1) ((canonicalQ _).mp hy.1)
 obtain ⟨b,hb,cb⟩ := qsub_total (toQ x.c1) (toQ y.c1) ((canonicalQ _).mp hx.2) ((canonicalQ _).mp hy.2)
 exact ⟨fromE (a,b),by simp only [sub,ha,hb,bind_tc_ok],fromE_canonical _ ⟨ca,cb⟩⟩
/-- The retained scalar theorem supplies exact natural products; no new
multiplication proof or native multiplication gate is performed. -/
theorem scale_total (x : Stage2E) (s : U32) :
 ∃ z, scale x s=ok z ∧ WideCanonical z := by
 obtain ⟨a,ha,ca,_,_,_,_⟩ := ExtractedMaskScalarMul.current_qm_mul_m31_mod (toQ x.c0) s
 obtain ⟨b,hb,cb,_,_,_,_⟩ := ExtractedMaskScalarMul.current_qm_mul_m31_mod (toQ x.c1) s
 exact ⟨fromE (a,b),by simp only [scale,ha,hb,bind_tc_ok],fromE_canonical _ ⟨ca,cb⟩⟩
#print axioms qsub_total
#print axioms sub_total
#print axioms scale_total
end NBO_FoldLinear
end
