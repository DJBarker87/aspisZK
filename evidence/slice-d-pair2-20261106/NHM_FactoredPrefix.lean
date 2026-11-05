import NHI_FactoredProducers
import NHI_RangeProgress
set_option autoImplicit false
noncomputable section
namespace NHM_FactoredPrefix
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues FIo_Native
abbrev Iter := NHI_RangeProgress.Range
abbrev Cells := Array NE 4#usize
abbrev State := Iter × Cells

/-- Source suffix after the retained eight-call producer packet. -/
def tail (ap0 ap1 : Array NE 4#usize) (side : Usize) (iter1 : Iter) (weights : Cells)
 (low_powers high_powers : Array NQ 4#usize) (q4 q16 : NQ) : Result (ControlFlow State Cells) := do
let low ←
  _root_.FIo_Native.weights.Weights.scalar_factor
    low_powers ap0
let i ← Array.index_usize _root_.FIo_Native.weights.PERM 0#usize
let we ← Array.index_usize ap1 i
let q5 ←
  Array.index_usize
    high_powers
    0#usize
let we1 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we q5
let term0 ←
  aspis_core.field.wide_exact.WideExact.mul_m31 we1 _root_.FIo_Native.weights.QUARTER
let i1 ← Array.index_usize _root_.FIo_Native.weights.PERM 1#usize
let we2 ← Array.index_usize ap1 i1
let q6 ←
  Array.index_usize
    high_powers
    1#usize
let we3 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we2 q6
let term1 ←
  aspis_core.field.wide_exact.WideExact.mul_m31 we3 _root_.FIo_Native.weights.QUARTER
let i2 ← Array.index_usize _root_.FIo_Native.weights.PERM 2#usize
let we4 ← Array.index_usize ap1 i2
let q7 ←
  Array.index_usize
    high_powers
    2#usize
let we5 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we4 q7
let term2 ←
  aspis_core.field.wide_exact.WideExact.mul_m31 we5 _root_.FIo_Native.weights.QUARTER
let i3 ← Array.index_usize _root_.FIo_Native.weights.PERM 3#usize
let we6 ← Array.index_usize ap1 i3
let q9 ←
  Array.index_usize
    high_powers
    3#usize
let we7 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we6 q9
let term3 ←
  aspis_core.field.wide_exact.WideExact.mul_m31 we7 _root_.FIo_Native.weights.QUARTER
let we8 ←
  Array.index_usize (Array.make 4#usize [ term0, term1, term2, term3 ])
    0#usize
let we9 ←
  Array.index_usize (Array.make 4#usize [ term0, term1, term2, term3 ])
    1#usize
let first2 ← aspis_core.field.wide_exact.WideExact.add we8 we9
let we10 ←
  Array.index_usize (Array.make 4#usize [ term0, term1, term2, term3 ])
    2#usize
let first3 ← aspis_core.field.wide_exact.WideExact.add first2 we10
let we11 ←
  Array.index_usize (Array.make 4#usize [ term0, term1, term2, term3 ])
    3#usize
let all ← aspis_core.field.wide_exact.WideExact.add first3 we11
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
  let we18 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we17 q4
  let weights2 ← Array.update weights1 2#usize we18
  let we19 ← aspis_core.field.wide_exact.WideExact.mul low first2
  let q10 ← aspis_core.field.QM31.mul q16 q4
  let we20 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we19 q10
  let a ← Array.update weights2 3#usize we20
  ok (cont (iter1, a))

def body (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize) (s : State) :
 Result (ControlFlow State Cells) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some side=>do
  let q ← Array.index_usize extra side
  let (low,high,q4,q16) ← NHI_FactoredProducers.run q
  tail ap0 ap1 side next s.2 low high q4 q16

theorem pick_two (q0 q1 q2 q3 : NQ) :
 Array.index_usize (Array.make 4#usize [q0,q1,q2,q3]) 2#usize=ok q2 := by rfl

/-- Complete source-order association, retaining the unused q^4 call and every
possible producer error. No successful-child or desired-output premise. -/
theorem source (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize) (s : State) :
 FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2=
 body ap0 ap1 extra s := by
 unfold FIo_Native.weights.factored_s2_libra_weights_loop.body body tail NHI_FactoredProducers.run
 simp only [NHI_FactoredProducers.one,bind_assoc_eq,bind_tc_ok,pick_two]
 rfl

#print axioms pick_two
#print axioms source
end NHM_FactoredPrefix
end
