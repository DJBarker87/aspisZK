import AspisV8R19.R181SampledChordGuard

/-! Selected chord arithmetic after the three batch evaluations. The third
batch value is an independent explicit input here: this leaf does not assume
that the actual captured fold repeated the first value. `inverseDifference`
factors the exact source sub/try_inv/ok_or sequence and retains Domain error. -/
set_option autoImplicit false
namespace AspisV8R19.R203ChordDataExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open R165QuarticExecution (Canonical decode encode_decode sub)
open R164ProductExecution (encode public_product)
noncomputable section
local instance : DecidableEq field.QM31 := Classical.decEq _

structure ChordData where
  iv : field.QM31 × field.QM31
  abc : field.QM31 × field.QM31 × field.QM31
  use_x : Bool

def rawData (s z : circle.SecureCirclePoint)
    (batch0 batch1 batch0Again : field.QM31) :
    Result (core.result.Result ChordData AspisR156FullFreeze.Error) := do
  let use_x ← core.cmp.PartialEq.ne.trait_default
    field.QM31.Insts.CoreCmpPartialEqQM31 s.x z.x
  let h0 ← if use_x then ok s.x else ok s.y
  let h1 ← if use_x then ok z.x else ok z.y
  let q2 ← field.QM31.sub batch0 batch1
  let inv ← R175ChordInverseExecution.inverseDifference h0 h1
  match inv with
  | .Err e => ok (.Err e)
  | .Ok val2 =>
    let slope ← field.QM31.mul q2 val2
    let q5 ← field.QM31.mul slope h0
    let q6 ← field.QM31.sub batch0Again q5
    let q7 ← field.QM31.mul s.x z.y
    let q8 ← field.QM31.mul s.y z.x
    let q9 ← field.QM31.sub q7 q8
    let q10 ← field.QM31.sub s.y z.y
    let q11 ← field.QM31.sub z.x s.x
    ok (.Ok ⟨(q6,slope),(q9,q10,q11),use_x⟩)

def exactData (s z : circle.SecureCirclePoint) (b0 b1 again : QM31Exact) : ChordData :=
  let coords := R175ChordInverseExecution.selectedCoordinates s z
  let slope := (b0-b1) * (decode coords.1 - decode coords.2)⁻¹
  ⟨(encode (again - slope * decode coords.1), encode slope),
    (encode (decode s.x * decode z.y - decode s.y * decode z.x),
      encode (decode s.y - decode z.y),encode (decode z.x - decode s.x)),
    decide (s.x ≠ z.x)⟩

theorem rawData_exact (s z : circle.SecureCirclePoint)
    (hsx : Canonical s.x) (hsy : Canonical s.y)
    (hzx : Canonical z.x) (hzy : Canonical z.y) (hsz : s ≠ z)
    (b0 b1 again : QM31Exact) :
    rawData s z (encode b0) (encode b1) (encode again) =
      .ok (.Ok (exactData s z b0 b1 again)) := by
  obtain ⟨hc0,hc1,hne⟩ := R175ChordInverseExecution.selectedCoordinates_valid
    s z hsx hsy hzx hzy hsz
  have hinv := R175ChordInverseExecution.inverseDifference_exact
    (R175ChordInverseExecution.selectedCoordinates s z).1
    (R175ChordInverseExecution.selectedCoordinates s z).2 hc0 hc1 hne
  have hx : s.x = encode (decode s.x) := (encode_decode s.x hsx).symm
  have hy : s.y = encode (decode s.y) := (encode_decode s.y hsy).symm
  have hz : z.x = encode (decode z.x) := (encode_decode z.x hzx).symm
  have hw : z.y = encode (decode z.y) := (encode_decode z.y hzy).symm
  by_cases hcoord : s.x = z.x
  · simp only [R175ChordInverseExecution.selectedCoordinates, hcoord, not_true_eq_false, if_false] at hinv
    simp only [rawData, R175ChordInverseExecution.raw_qm31_ne, hcoord,
      ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
      bind_tc_ok, sub, hinv]
    rw [hy,hx,hz,hw]
    simp only [public_product, sub, bind_tc_ok, exactData,
      R175ChordInverseExecution.selectedCoordinates, hcoord,
      not_true_eq_false, if_false, decode_encode, decide_false]
  · simp only [R175ChordInverseExecution.selectedCoordinates, hcoord, if_true] at hinv
    simp only [rawData, R175ChordInverseExecution.raw_qm31_ne, hcoord,
      ne_eq, not_false_eq_true, decide_true, if_true, bind_tc_ok, sub, hinv]
    rw [hx,hy,hz,hw]
    simp only [public_product, sub, bind_tc_ok, exactData,
      R175ChordInverseExecution.selectedCoordinates, hcoord, if_true,
      decode_encode, decide_true]

#print axioms rawData_exact
end
end AspisV8R19.R203ChordDataExecution
