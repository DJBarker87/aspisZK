import SAQ_WideABI
import R17CurrentDomainCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_RawCM
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
abbrev C := field.CM31
def Canon (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

theorem add_exact (x y z : C) (h : field.CM31.add x y=ok z) :
    decodeC z=decodeC x+decodeC y := by
  unfold field.CM31.add at h
  obtain ⟨a,ha,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have same : (⟨a,b⟩ : C)=z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact m31_add_exact x.a y.a a ha
  · exact m31_add_exact x.b y.b b hb

theorem mul_exact (x y z : C) (h : field.CM31.mul x y=ok z) :
    Canon z ∧ decodeC z=decodeC x*decodeC y := by
  have hm := cm_mul_same x y
  rw [h,bind_tc_ok] at hm
  have hr := R17CurrentCM31Semantics.current_cm31_mul_decode (toCM x) (toCM y) (toCM z) hm.symm
  have hc := R17CurrentDomainCanonical.arithmetic_cm_mul_success_canonical
    (toCM x) (toCM y) (toCM z) hm.symm
  refine ⟨hc,?_⟩
  apply QuadraticAlgebra.ext
  · exact congrArg Prod.fst hr
  · exact congrArg Prod.snd hr

theorem add_canonical (x y z : C) (hx : Canon x) (hy : Canon y)
    (h : field.CM31.add x y=ok z) : Canon z := by
  have hm := cm_add_same x y
  rw [h,bind_tc_ok] at hm
  obtain ⟨out,ho,hc,_,_⟩ := ExtractedCurrentTowerAdd.current_cm_add_mod (toCM x) (toCM y) hx hy
  have same : toCM z=out := Result.ok.inj (hm.trans ho)
  change ExtractedCurrentTowerAdd.CanonicalCM (toCM z)
  rw [same]
  exact hc

theorem sub_canonical (x y z : C) (hx : Canon x) (hy : Canon y)
    (h : field.CM31.sub x y=ok z) : Canon z := by
  have hm := cm_sub_same x y
  rw [h,bind_tc_ok] at hm
  obtain ⟨out,ho,hc,_,_⟩ := ExtractedCurrentTowerAdd.current_cm_sub_mod (toCM x) (toCM y) hx hy
  have same : toCM z=out := Result.ok.inj (hm.trans ho)
  change ExtractedCurrentTowerAdd.CanonicalCM (toCM z)
  rw [same]
  exact hc

theorem by_r_canonical (x z : C) (hx : Canon x)
    (h : field.mul_by_r x=ok z) : Canon z := by
  have hm := mul_by_r_same x
  rw [h,bind_tc_ok] at hm
  obtain ⟨out,ho,hc⟩ := AspisR1CurrentWideMul.by_r_total (toCM x) hx
  have same : toCM z=out := Result.ok.inj (hm.trans ho)
  change ExtractedCurrentTowerAdd.CanonicalCM (toCM z)
  rw [same]
  exact hc

#print axioms add_exact
#print axioms mul_exact
#print axioms add_canonical
#print axioms sub_canonical
#print axioms by_r_canonical
end AspisR1.SAQ_RawCM
end
