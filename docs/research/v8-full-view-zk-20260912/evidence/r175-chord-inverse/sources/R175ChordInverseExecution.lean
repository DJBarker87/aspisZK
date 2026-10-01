import AspisV8R19.R166CircleExecution

set_option autoImplicit false
namespace AspisV8R19.R175ChordInverseExecution

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R19.R165QuarticExecution (Canonical decode encode_decode sub try_inverse_nonzero)
open AspisV8R19.R164ProductExecution (encode)

noncomputable section
local instance : DecidableEq field.CM31 := Classical.decEq _
local instance : DecidableEq field.QM31 := Classical.decEq _
local instance : DecidableEq circle.SecureCirclePoint := Classical.decEq _

theorem raw_cm31_eq (a b : field.CM31) :
    field.CM31.Insts.CoreCmpPartialEqCM31.eq a b = .ok (decide (a = b)) := by
  cases a with
  | mk a0 a1 =>
    cases b with
    | mk b0 b1 =>
      by_cases h : a0 = b0 <;>
        simp [field.CM31.Insts.CoreCmpPartialEqCM31.eq,
          field.M31.Insts.CoreCmpPartialEqM31.eq, bind_tc_ok, field.CM31.mk.injEq, h]

theorem raw_qm31_eq (a b : field.QM31) :
    field.QM31.Insts.CoreCmpPartialEqQM31.eq a b = .ok (decide (a = b)) := by
  cases a with
  | mk a0 a1 =>
    cases b with
    | mk b0 b1 =>
      by_cases h : a0 = b0 <;>
        simp [field.QM31.Insts.CoreCmpPartialEqQM31.eq,
          raw_cm31_eq, bind_tc_ok, field.QM31.mk.injEq, h]

theorem raw_secure_circle_point_eq (a b : circle.SecureCirclePoint) :
    circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq a b =
      .ok (decide (a = b)) := by
  cases a with
  | mk ax ay =>
    cases b with
    | mk bx bY =>
      by_cases h : ax = bx <;>
        simp [circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq,
          raw_qm31_eq, bind_tc_ok, circle.SecureCirclePoint.mk.injEq, h]

theorem raw_qm31_ne (a b : field.QM31) :
    core.cmp.PartialEq.ne.trait_default
      field.QM31.Insts.CoreCmpPartialEqQM31 a b = .ok (decide (a ≠ b)) := by
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default, raw_qm31_eq, bind_tc_ok]

theorem canonical_difference_nonzero (a b : field.QM31)
    (ha : Canonical a) (hb : Canonical b) (hab : a ≠ b) :
    decode a - decode b ≠ 0 := by
  intro hzero
  have hdecode : decode a = decode b := sub_eq_zero.mp hzero
  have hsource : a = b := by
    calc
      a = encode (decode a) := (encode_decode a ha).symm
      _ = encode (decode b) := congrArg encode hdecode
      _ = b := encode_decode b hb
  exact hab hsource

def inverseDifference (a b : field.QM31) :
    Result (core.result.Result field.QM31 AspisR156FullFreeze.Error) := do
  let d ← field.QM31.sub a b
  let inv ← field.QM31.try_inv d
  AspisR156FullFreeze.core.option.Option.ok_or inv AspisR156FullFreeze.Error.Domain

theorem inverseDifference_exact (a b : field.QM31)
    (ha : Canonical a) (hb : Canonical b) (hab : a ≠ b) :
    inverseDifference a b = .ok (.Ok (encode ((decode a - decode b)⁻¹))) := by
  have hdiff : decode a - decode b ≠ 0 :=
    canonical_difference_nonzero a b ha hb hab
  have hsub : field.QM31.sub a b = .ok (encode (decode a - decode b)) := by
    conv_lhs => rw [← encode_decode a ha, ← encode_decode b hb]
    exact sub (decode a) (decode b)
  have hinv : field.QM31.try_inv (encode (decode a - decode b)) =
      .ok (some (encode ((decode a - decode b)⁻¹))) :=
    try_inverse_nonzero _ hdiff
  simp only [inverseDifference, hsub, bind_tc_ok, hinv,
    AspisR156FullFreeze.core.option.Option.ok_or]

#print axioms raw_cm31_eq
#print axioms raw_qm31_eq
#print axioms raw_secure_circle_point_eq
#print axioms raw_qm31_ne
#print axioms canonical_difference_nonzero
#print axioms inverseDifference_exact

def selectedCoordinates (s z : circle.SecureCirclePoint) : field.QM31 × field.QM31 :=
  if s.x ≠ z.x then (s.x, z.x) else (s.y, z.y)

def rawChordInverse (s z : circle.SecureCirclePoint) :
    Result (core.result.Result field.QM31 AspisR156FullFreeze.Error) := do
  let use_x ← core.cmp.PartialEq.ne.trait_default
    field.QM31.Insts.CoreCmpPartialEqQM31 s.x z.x
  let h0 ← if use_x then ok s.x else ok s.y
  let h1 ← if use_x then ok z.x else ok z.y
  inverseDifference h0 h1

theorem rawChordInverse_factored (s z : circle.SecureCirclePoint) :
    rawChordInverse s z =
      inverseDifference (selectedCoordinates s z).1 (selectedCoordinates s z).2 := by
  by_cases hx : s.x = z.x <;>
    simp [rawChordInverse, selectedCoordinates, raw_qm31_ne, hx, bind_tc_ok]

theorem selectedCoordinates_valid (s z : circle.SecureCirclePoint)
    (hsx : Canonical s.x) (hsy : Canonical s.y)
    (hzx : Canonical z.x) (hzy : Canonical z.y) (hsz : s ≠ z) :
    Canonical (selectedCoordinates s z).1 ∧
      Canonical (selectedCoordinates s z).2 ∧
      (selectedCoordinates s z).1 ≠ (selectedCoordinates s z).2 := by
  by_cases hx : s.x = z.x
  · have hy : s.y ≠ z.y := by
      intro hy
      apply hsz
      cases s with
      | mk sx sy =>
        cases z with
        | mk zx zy =>
          simp_all [circle.SecureCirclePoint.mk.injEq]
    simp [selectedCoordinates, hx, hsy, hzy, hy]
  · simp [selectedCoordinates, hx, hsx, hzx]

theorem rawChordInverse_exact (s z : circle.SecureCirclePoint)
    (hsx : Canonical s.x) (hsy : Canonical s.y)
    (hzx : Canonical z.x) (hzy : Canonical z.y) (hsz : s ≠ z) :
    rawChordInverse s z =
      .ok (.Ok (encode ((decode (selectedCoordinates s z).1 -
        decode (selectedCoordinates s z).2)⁻¹))) := by
  rw [rawChordInverse_factored]
  rcases selectedCoordinates_valid s z hsx hsy hzx hzy hsz with ⟨ha, hb, hab⟩
  exact inverseDifference_exact _ _ ha hb hab

#print axioms rawChordInverse_factored
#print axioms selectedCoordinates_valid
#print axioms rawChordInverse_exact
end
end AspisV8R19.R175ChordInverseExecution
