import R1Z.PV_RunJoin_WeightAbsorption46
import R1Z.PV_RunJoin_WeightConstructorShape46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStages47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_B2_C_WeightsNative
abbrev Point := Array K 10#usize
abbrev Points := Array Point 3#usize

def finish (z out : Point) (bit7 : K) : Result Points := do
  let q ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit7
  let z1 ← Array.update z 7#usize q
  let b ← Array.index_usize z1 6#usize
  let q1 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b
  let z2 ← Array.update z1 6#usize q1
  ok (Array.make 3#usize [z,out,z2])

def stage0 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 0#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 0#usize q2
  finish z out1 bit7

def stage1 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 1#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 1#usize q2
  stage0 z out1 bc bit7

def stage2 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 2#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 2#usize q2
  stage1 z out1 bc bit7

def stage3 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 3#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 3#usize q2
  stage2 z out1 bc bit7

def stage4 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 4#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 4#usize q2
  stage3 z out1 bc bit7

def stage5 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 5#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 5#usize q2
  stage4 z out1 bc bit7

def stage6 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 6#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 6#usize q2
  stage5 z out1 bc bit7

def stage7 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 7#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 7#usize q2
  stage6 z out1 bc bit

def stage8 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 8#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 8#usize q2
  stage7 z out1 bc bit7

def stage9 (z out : Point) (carry bit7 : K) : Result Points := do
  let bit ← Array.index_usize z 9#usize
  let bc ← aspis_core.field.QM31.mul bit carry
  let q ← aspis_core.field.QM31.add bit carry
  let q1 ← aspis_core.field.QM31.add bc bc
  let q2 ← aspis_core.field.QM31.sub q q1
  let out1 ← Array.update out 9#usize q2
  stage8 z out1 bc bit7

attribute [local irreducible] aspis_core.field.QM31.mul aspis_core.field.QM31.add
  aspis_core.field.QM31.sub

theorem source (z : Point) : host_weights.state_only_statement_points z=
    stage9 z z aspis_core.field.QM31.ONE aspis_core.field.QM31.ZERO := by rfl
#print axioms source
end R1Z.PV_RunJoin_WeightPointsStages47
