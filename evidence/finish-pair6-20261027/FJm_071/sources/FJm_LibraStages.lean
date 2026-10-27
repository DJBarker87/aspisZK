import FJm_QMSquare
import FJg_ScalarValue
import FIo_MixedValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraStages
open Aeneas Aeneas.Std Result ControlFlow FIo_Native
open FIo_FieldBridge (NQ NE)
abbrev Weights := Array NE 4#usize
abbrev State := FIo_RangeNext.Range × Weights

def powers (extra : Array NQ 2#usize) (side : Usize) :
    Result (Array NQ 4#usize × Array NQ 4#usize × NQ × NQ) := do
  let q ← Array.index_usize extra side
  let q1 ← aspis_core.field.QM31.mul aspis_core.field.QM31.ONE q
  let q2 ← aspis_core.field.QM31.mul q1 q
  let q3 ← aspis_core.field.QM31.mul q2 q
  let _ ← aspis_core.field.QM31.mul q3 q
  let q4 ←
    Array.index_usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, q1, q2, q3 ]) 2#usize
  let q41 ← aspis_core.field.QM31.square q4
  let q8 ← aspis_core.field.QM31.square q41
  let q12 ← aspis_core.field.QM31.mul q8 q41
  let q16 ← aspis_core.field.QM31.square q8
  ok (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3],
    Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12],q41,q16)

def term (ap1 : Weights) (high : Array NQ 4#usize) (j : Usize) : Result (Usize × NE) := do
  let i ← Array.index_usize FIo_Native.weights.PERM j
  let we ← Array.index_usize ap1 i
  let q ← Array.index_usize high j
  let we1 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we q
  let term ← aspis_core.field.wide_exact.WideExact.mul_m31 we1 FIo_Native.weights.QUARTER
  ok (i,term)

def totals (terms : Weights) : Result (NE × NE × NE) := do
  let we8 ← Array.index_usize terms 0#usize
  let we9 ← Array.index_usize terms 1#usize
  let first2 ← aspis_core.field.wide_exact.WideExact.add we8 we9
  let we10 ← Array.index_usize terms 2#usize
  let first3 ← aspis_core.field.wide_exact.WideExact.add first2 we10
  let we11 ← Array.index_usize terms 3#usize
  let all ← aspis_core.field.wide_exact.WideExact.add first3 we11
  ok (first2,first3,all)

def finish (side : Usize) (low : NE) (i3 : Usize) (first2 first3 all : NE) (q41 q16 : NQ)
    (ap1 weights : Weights) (iter1 : FIo_RangeNext.Range) : Result (ControlFlow State Weights) := do
  if side = 0#usize
  then
    let we12 ← aspis_core.field.wide_exact.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we12
    let we13 ← aspis_core.field.wide_exact.WideExact.mul low first3
    let we14 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we13 q16
    let a ← Array.update weights1 1#usize we14
    ok (cont (iter1, a))
  else
    let we12 ← Array.index_usize weights 1#usize
    let we13 ← Array.index_usize ap1 i3
    let we14 ←
      aspis_core.field.wide_exact.WideExact.mul_m31 we13 _root_.FIo_Native.weights.QUARTER
    let we15 ← aspis_core.field.wide_exact.WideExact.mul low we14
    let we16 ← aspis_core.field.wide_exact.WideExact.add we12 we15
    let weights1 ← Array.update weights 1#usize we16
    let we17 ← aspis_core.field.wide_exact.WideExact.mul low all
    let we18 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we17 q41
    let weights2 ← Array.update weights1 2#usize we18
    let we19 ← aspis_core.field.wide_exact.WideExact.mul low first2
    let q10 ← aspis_core.field.QM31.mul q16 q41
    let we20 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we19 q10
    let a ← Array.update weights2 3#usize we20
    ok (cont (iter1, a))

def body (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights : Weights) : Result (ControlFlow State Weights) := do
  let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none=>ok (.done weights)
  | some side=> do
    let (base,high,q41,q16) ← powers extra side
    let low ← FIo_Native.weights.Weights.scalar_factor base ap0
    let (_,term0) ← term ap1 high 0#usize
    let (_,term1) ← term ap1 high 1#usize
    let (_,term2) ← term ap1 high 2#usize
    let (i3,term3) ← term ap1 high 3#usize
    let (first2,first3,all) ← totals (Array.make 4#usize [term0,term1,term2,term3])
    finish side low i3 first2 first3 all q41 q16 ap1 weights iter1

theorem body_eq (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights : Weights) :
    FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      body ap0 ap1 extra iter weights := by
  simp only [FIo_Native.weights.factored_s2_libra_weights_loop.body,body,powers,term,totals,finish,
    bind_assoc_eq,bind_tc_ok,lift]
#print axioms body_eq
end AspisR1.FJm_LibraStages
end
