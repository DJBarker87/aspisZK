import R22CanonicalCM31

/-! R22 compositional lift from exact checked/wrapping CM31 equality to the
actual current QM31 add/mul and mul_by_r source bodies. -/
set_option autoImplicit false
namespace AspisR1.R22CanonicalQM31
open Aeneas Aeneas.Std Result
open R22CanonicalM31AddSub R22CurrentReducerMul R22CanonicalCM31
open ExtractedCurrentTowerAdd
abbrev CM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev QM := AspisR1Qm31ArithmeticProbe.field.QM31

def wrappingByR (x : CM) : CM :=
  ⟨wrappingSub (wrappingAdd x.a x.a) x.b,
    wrappingAdd x.a (wrappingAdd x.b x.b)⟩

theorem byR_agrees (x : CM) (hx : CanonicalCM x) :
    AspisR1Qm31ArithmeticProbe.field.mul_by_r x = ok (wrappingByR x) := by
  have ha := wrapping_add_canonical x.a x.a hx.1 hx.1
  have hb := wrapping_add_canonical x.b x.b hx.2 hx.2
  simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
    AspisR1Qm31ArithmeticProbe.field.M31.double,
    canonical_add_agrees _ _ hx.1 hx.1,canonical_add_agrees _ _ hx.2 hx.2,
    bind_tc_ok,canonical_sub_agrees _ _ ha hx.2,
    canonical_add_agrees _ _ hx.1 hb,wrappingByR]

theorem byR_canonical (x : CM) (hx : CanonicalCM x) : CanonicalCM (wrappingByR x) :=
  ⟨wrapping_sub_canonical _ _ (wrapping_add_canonical _ _ hx.1 hx.1) hx.2,
   wrapping_add_canonical _ _ hx.1 (wrapping_add_canonical _ _ hx.2 hx.2)⟩

def wrappingQMAdd (x y : QM) : QM :=
  ⟨wrappingCMAdd x.c0 y.c0,wrappingCMAdd x.c1 y.c1⟩

theorem qm_add_agrees (x y : QM) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    AspisR1Qm31ArithmeticProbe.field.QM31.add x y = ok (wrappingQMAdd x y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.QM31.add,
    cm_add_agrees _ _ hx.1 hy.1,cm_add_agrees _ _ hx.2 hy.2,bind_tc_ok,wrappingQMAdd]

theorem qm_add_canonical (x y : QM) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    CanonicalQM (wrappingQMAdd x y) :=
  ⟨cm_add_canonical _ _ hx.1 hy.1,cm_add_canonical _ _ hx.2 hy.2⟩

def wrappingQMMul (x y : QM) : QM :=
  let m0 := wrappingCMMul x.c0 y.c0
  let m1 := wrappingCMMul x.c1 y.c1
  let m2 := wrappingCMMul (wrappingCMAdd x.c0 x.c1) (wrappingCMAdd y.c0 y.c1)
  ⟨wrappingCMAdd m0 (wrappingByR m1),wrappingCMSub (wrappingCMSub m2 m0) m1⟩

theorem qm_mul_agrees (x y : QM) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    AspisR1Qm31ArithmeticProbe.field.QM31.mul x y = ok (wrappingQMMul x y) := by
  have h0 := cm_mul_canonical _ _ hx.1 hy.1
  have h1 := cm_mul_canonical _ _ hx.2 hy.2
  have hs0 := cm_add_canonical _ _ hx.1 hx.2
  have hs1 := cm_add_canonical _ _ hy.1 hy.2
  have h2 := cm_mul_canonical _ _ hs0 hs1
  have hr := byR_canonical _ h1
  have hh := cm_sub_canonical _ _ h2 h0
  simp only [AspisR1Qm31ArithmeticProbe.field.QM31.mul,
    cm_mul_agrees _ _ hx.1 hy.1,cm_mul_agrees _ _ hx.2 hy.2,
    cm_add_agrees _ _ hx.1 hx.2,cm_add_agrees _ _ hy.1 hy.2,
    bind_tc_ok,cm_mul_agrees _ _ hs0 hs1,byR_agrees _ h1,
    cm_add_agrees _ _ h0 hr,cm_sub_agrees _ _ h2 h0,cm_sub_agrees _ _ hh h1,
    wrappingQMMul]

theorem qm_mul_canonical (x y : QM) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    CanonicalQM (wrappingQMMul x y) := by
  have h0 := cm_mul_canonical _ _ hx.1 hy.1
  have h1 := cm_mul_canonical _ _ hx.2 hy.2
  have h2 := cm_mul_canonical _ _ (cm_add_canonical _ _ hx.1 hx.2)
    (cm_add_canonical _ _ hy.1 hy.2)
  exact ⟨cm_add_canonical _ _ h0 (byR_canonical _ h1),
    cm_sub_canonical _ _ (cm_sub_canonical _ _ h2 h0) h1⟩

#print axioms byR_agrees
#print axioms byR_canonical
#print axioms qm_add_agrees
#print axioms qm_add_canonical
#print axioms qm_mul_agrees
#print axioms qm_mul_canonical
end AspisR1.R22CanonicalQM31
