import V7ProductionCallbacksR30FieldCanonical

/-!
# Canonicality of the production callback's secure-field primitives

The callback carries the same concrete field representation as the R26 model,
but its generated checked-arithmetic code is separate.  This module composes
the audited callback base and complex operations for the QM31 operations used
by the query callback.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26FieldBridge

namespace V7ProductionCallbacksR30Qm31Canonical

open V7ProductionCallbacksR30FieldCanonical

abbrev CallbackM31 := V7ProductionCallbacksR29.aspis_core.field.M31
abbrev CallbackCM31 := V7ProductionCallbacksR29.aspis_core.field.CM31
abbrev CallbackQM31 := V7ProductionCallbacksR29.aspis_core.field.QM31

theorem callback_cm31_add_canonical
    (left right : CallbackCM31)
    (hleft : GeneratedCanonicalCM31 left)
    (hright : GeneratedCanonicalCM31 right) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.add left right = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨real, hreal, hrealCanonical⟩ :=
    callback_m31_add_canonical left.a right.a hleft.1 hright.1
  obtain ⟨imag, himag, himagCanonical⟩ :=
    callback_m31_add_canonical left.b right.b hleft.2 hright.2
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨hrealCanonical, himagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.CM31.add,
    hreal, himag, output]

theorem callback_cm31_sub_canonical
    (left right : CallbackCM31)
    (hleft : GeneratedCanonicalCM31 left)
    (hright : GeneratedCanonicalCM31 right) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.CM31.sub left right = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨real, hreal, hrealCanonical⟩ :=
    callback_m31_sub_canonical left.a right.a hleft.1 hright.1
  obtain ⟨imag, himag, himagCanonical⟩ :=
    callback_m31_sub_canonical left.b right.b hleft.2 hright.2
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨hrealCanonical, himagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.CM31.sub,
    hreal, himag, output]

theorem callback_mul_by_r_canonical
    (value : CallbackCM31)
    (canonical : GeneratedCanonicalCM31 value) :
    ∃ output : CallbackCM31,
      V7ProductionCallbacksR29.aspis_core.field.mul_by_r value = ok output ∧
      GeneratedCanonicalCM31 output := by
  obtain ⟨twiceReal, htwiceReal, twiceRealCanonical⟩ :=
    callback_m31_double_canonical value.a canonical.1
  obtain ⟨real, hreal, realCanonical⟩ :=
    callback_m31_sub_canonical twiceReal value.b twiceRealCanonical canonical.2
  obtain ⟨twiceImag, htwiceImag, twiceImagCanonical⟩ :=
    callback_m31_double_canonical value.b canonical.2
  obtain ⟨imag, himag, imagCanonical⟩ :=
    callback_m31_add_canonical value.a twiceImag canonical.1 twiceImagCanonical
  let output : CallbackCM31 := ⟨real, imag⟩
  refine ⟨output, ?_, ⟨realCanonical, imagCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.mul_by_r,
    htwiceReal, hreal, htwiceImag, himag, output]

theorem callback_qm31_add_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.add left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_add_canonical left.c1 right.c1 hleft.2 hright.2
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.add,
    hlow, hhigh, output]

theorem callback_qm31_sub_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.sub left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_sub_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_sub_canonical left.c1 right.c1 hleft.2 hright.2
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.sub,
    hlow, hhigh, output]

theorem callback_qm31_mul_canonical
    (left right : CallbackQM31)
    (hleft : GeneratedCanonicalQM31 left)
    (hright : GeneratedCanonicalQM31 right) :
    ∃ output : CallbackQM31,
      V7ProductionCallbacksR29.aspis_core.field.QM31.mul left right = ok output ∧
      GeneratedCanonicalQM31 output := by
  obtain ⟨m0, hm0, m0Canonical⟩ :=
    callback_cm31_mul_canonical left.c0 right.c0 hleft.1 hright.1
  obtain ⟨m1, hm1, m1Canonical⟩ :=
    callback_cm31_mul_canonical left.c1 right.c1 hleft.2 hright.2
  obtain ⟨leftSum, hleftSum, leftSumCanonical⟩ :=
    callback_cm31_add_canonical left.c0 left.c1 hleft.1 hleft.2
  obtain ⟨rightSum, hrightSum, rightSumCanonical⟩ :=
    callback_cm31_add_canonical right.c0 right.c1 hright.1 hright.2
  obtain ⟨m2, hm2, m2Canonical⟩ :=
    callback_cm31_mul_canonical leftSum rightSum leftSumCanonical rightSumCanonical
  obtain ⟨rM1, hrM1, rM1Canonical⟩ :=
    callback_mul_by_r_canonical m1 m1Canonical
  obtain ⟨low, hlow, lowCanonical⟩ :=
    callback_cm31_add_canonical m0 rM1 m0Canonical rM1Canonical
  obtain ⟨imagPart, himagPart, imagPartCanonical⟩ :=
    callback_cm31_sub_canonical m2 m0 m2Canonical m0Canonical
  obtain ⟨high, hhigh, highCanonical⟩ :=
    callback_cm31_sub_canonical imagPart m1 imagPartCanonical m1Canonical
  let output : CallbackQM31 := ⟨low, high⟩
  refine ⟨output, ?_, ⟨lowCanonical, highCanonical⟩⟩
  simp [V7ProductionCallbacksR29.aspis_core.field.QM31.mul,
    hm0, hm1, hleftSum, hrightSum, hm2, hrM1, hlow, himagPart,
    hhigh, output]

#print axioms callback_cm31_add_canonical
#print axioms callback_cm31_sub_canonical
#print axioms callback_mul_by_r_canonical
#print axioms callback_qm31_add_canonical
#print axioms callback_qm31_sub_canonical
#print axioms callback_qm31_mul_canonical

end V7ProductionCallbacksR30Qm31Canonical
