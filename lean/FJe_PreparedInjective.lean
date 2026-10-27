import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PreparedInjective
open Aeneas Aeneas.Std Result
open ExtractedMaskPreparedState
/-- A prepared component retains both original words without reduction. -/
theorem component (a : Component) (x y : CM) (hx : ComponentFor a x)
    (hy : ComponentFor a y) : x=y := by
  obtain ⟨s,hs,_,_⟩ := hx
  obtain ⟨t,ht,_,_⟩ := hy
  have h := congrArg Subtype.val (hs.symm.trans ht)
  change [x.a,x.b,s]=[y.a,y.b,t] at h
  simp only [List.cons.injEq] at h
  cases x;cases y
  cases h.1;cases h.2.1
  rfl
/-- The prepared witness is unique,so existential sum3 witnesses cannot select
weights different from the actual parsed operands. -/
theorem prepared (p : Prepared) (x y : QM) (hx : PreparedFor p x)
    (hy : PreparedFor p y) : x=y := by
  obtain ⟨_,a,b,c,_,_,ha,hb,_,hp⟩ := hx
  obtain ⟨_,a1,b1,c1,_,_,ha1,hb1,_,hp1⟩ := hy
  have h := congrArg Subtype.val (hp.symm.trans hp1)
  change [a,b,c]=[a1,b1,c1] at h
  simp only [List.cons.injEq] at h
  have e0 := component a x.c0 y.c0 ha (h.1.symm ▸ ha1)
  have e1 := component b x.c1 y.c1 hb (h.2.1.symm ▸ hb1)
  cases x;cases y
  cases e0;cases e1
  rfl
#print axioms component
#print axioms prepared
end AspisR1.FJe_PreparedInjective
end
