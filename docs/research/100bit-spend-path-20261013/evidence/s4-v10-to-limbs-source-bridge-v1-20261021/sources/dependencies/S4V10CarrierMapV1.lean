import AspisR1FastDotsMinimalFixedCallsV10.Types
import EbyKPushExplicitTypesV1

namespace AspisR1FastDotsV10CarrierMapV1

open Aeneas Aeneas.Std

abbrev V10M31 := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.M31
abbrev V10CM31 := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.CM31
abbrev V10QM31 := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.QM31
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

abbrev EKM31 := AspisR1EbyKPushCutV3.field.M31
abbrev EKCM31 := AspisR1EbyKPushCutV3.field.CM31
abbrev EKQM31 := AspisR1EbyKPushCutV3.field.QM31
abbrev EKWide := AspisR1EbyKPushCutV3.field.wide_exact.WideExact

def m31ToEbyK (x : V10M31) : EKM31 := x
def m31FromEbyK (x : EKM31) : V10M31 := x

def cm31ToEbyK (x : V10CM31) : EKCM31 := ⟨m31ToEbyK x.a, m31ToEbyK x.b⟩
def cm31FromEbyK (x : EKCM31) : V10CM31 := ⟨m31FromEbyK x.a, m31FromEbyK x.b⟩

def qm31ToEbyK (x : V10QM31) : EKQM31 := ⟨cm31ToEbyK x.c0, cm31ToEbyK x.c1⟩
def qm31FromEbyK (x : EKQM31) : V10QM31 := ⟨cm31FromEbyK x.c0, cm31FromEbyK x.c1⟩

def wideToEbyK (x : V10Wide) : EKWide := ⟨qm31ToEbyK x.c0, qm31ToEbyK x.c1⟩
def wideFromEbyK (x : EKWide) : V10Wide := ⟨qm31FromEbyK x.c0, qm31FromEbyK x.c1⟩

theorem m31_roundtrip (x : V10M31) : m31FromEbyK (m31ToEbyK x) = x := rfl
theorem m31_roundtrip' (x : EKM31) : m31ToEbyK (m31FromEbyK x) = x := rfl

theorem cm31_roundtrip (x : V10CM31) : cm31FromEbyK (cm31ToEbyK x) = x := by cases x; rfl
theorem cm31_roundtrip' (x : EKCM31) : cm31ToEbyK (cm31FromEbyK x) = x := by cases x; rfl

theorem qm31_roundtrip (x : V10QM31) : qm31FromEbyK (qm31ToEbyK x) = x := by cases x; rfl
theorem qm31_roundtrip' (x : EKQM31) : qm31ToEbyK (qm31FromEbyK x) = x := by cases x; rfl

theorem wide_roundtrip (x : V10Wide) : wideFromEbyK (wideToEbyK x) = x := by cases x; rfl
theorem wide_roundtrip' (x : EKWide) : wideToEbyK (wideFromEbyK x) = x := by cases x; rfl

def wideCarrierEquiv : V10Wide ≃ EKWide where
  toFun := wideToEbyK
  invFun := wideFromEbyK
  left_inv := wide_roundtrip
  right_inv := wide_roundtrip'

def wideCoordinatesV10 (x : V10Wide) : List U32 :=
  [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
   x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]

def wideCoordinatesEbyK (x : EKWide) : List U32 :=
  [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
   x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]

theorem wide_coordinates_preserved (x : V10Wide) :
    wideCoordinatesEbyK (wideToEbyK x) = wideCoordinatesV10 x := rfl

theorem wide_c0_map (x : V10Wide) : (wideToEbyK x).c0 = qm31ToEbyK x.c0 := rfl
theorem wide_c1_map (x : V10Wide) : (wideToEbyK x).c1 = qm31ToEbyK x.c1 := rfl
theorem qm_c0_map (x : V10QM31) : (qm31ToEbyK x).c0 = cm31ToEbyK x.c0 := rfl
theorem qm_c1_map (x : V10QM31) : (qm31ToEbyK x).c1 = cm31ToEbyK x.c1 := rfl
theorem cm_a_map (x : V10CM31) : (cm31ToEbyK x).a = m31ToEbyK x.a := rfl
theorem cm_b_map (x : V10CM31) : (cm31ToEbyK x).b = m31ToEbyK x.b := rfl

end AspisR1FastDotsV10CarrierMapV1

#print axioms AspisR1FastDotsV10CarrierMapV1.wideCarrierEquiv
#print axioms AspisR1FastDotsV10CarrierMapV1.wide_coordinates_preserved
