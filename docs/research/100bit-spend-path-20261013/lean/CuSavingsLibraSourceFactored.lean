import CuSavingsLibraSourceTerms
import CuSavingsLibra
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceFactored
open Aeneas Aeneas.Std Result ControlFlow AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
variable [Shared]
abbrev Points := Array E 4#usize
abbrev Powers := Array K 4#usize

structure Prepared where
  low : E
  first2 : E
  first3 : E
  all : E
  q4 : K
  q16 : K

def prepare (ap0 ap1 : Points) (q : K) : Result Prepared := do
  let powers ← kpowers 4#usize q
  let q2 ← Array.index_usize powers 2#usize
  let q4 ← field.QM31.square q2
  let q8 ← field.QM31.square q4
  let q12 ← field.QM31.mul q8 q4
  let q16 ← field.QM31.square q8
  let low ← Weights.scalar_factor powers ap0
  let terms ← AspisR1Libra.core.array.from_fn 4#usize
    new.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    (ap1,Array.make 4#usize [field.QM31.ONE,q4,q8,q12])
  let term0 ← Array.index_usize terms 0#usize
  let term1 ← Array.index_usize terms 1#usize
  let first2 ← field.wide_exact.WideExact.add term0 term1
  let term2 ← Array.index_usize terms 2#usize
  let first3 ← field.wide_exact.WideExact.add first2 term2
  let term3 ← Array.index_usize terms 3#usize
  let all ← field.wide_exact.WideExact.add first3 term3
  .ok ⟨low,first2,first3,all,q4,q16⟩

def side0 (data : Prepared) (weights : Points) : Result Points := do
  let value0 ← field.wide_exact.WideExact.mul data.low data.all
  let weights ← Array.update weights 0#usize value0
  let value1 ← field.wide_exact.WideExact.mul data.low data.first3
  let value1 ← field.wide_exact.WideExact.mul_qm31 value1 data.q16
  Array.update weights 1#usize value1

def side1 (ap1 : Points) (data : Prepared) (weights : Points) : Result Points := do
  let previous ← Array.index_usize weights 1#usize
  let index ← Array.index_usize new.PERM 3#usize
  let point ← Array.index_usize ap1 index
  let tail ← field.wide_exact.WideExact.mul_m31 point new.QUARTER
  let value1 ← field.wide_exact.WideExact.mul data.low tail
  let value1 ← field.wide_exact.WideExact.add previous value1
  let weights ← Array.update weights 1#usize value1
  let value2 ← field.wide_exact.WideExact.mul data.low data.all
  let value2 ← field.wide_exact.WideExact.mul_qm31 value2 data.q4
  let weights ← Array.update weights 2#usize value2
  let value3 ← field.wide_exact.WideExact.mul data.low data.first2
  let scalar ← field.QM31.mul data.q16 data.q4
  let value3 ← field.wide_exact.WideExact.mul_qm31 value3 scalar
  Array.update weights 3#usize value3

theorem bind_if {T U : Type} (condition : Prop) [Decidable condition]
    (yes no : Result T) (next : T → Result U) :
    (do let value ← if condition then yes else no
        next value) =
      if condition then (do let value ← yes;next value)
      else (do let value ← no;next value) := by
  by_cases h : condition <;> simp only [h,↓reduceIte]

/-- Exact factoring of the complete emitted loop body. The arithmetic and
array operations are unchanged; the shared prefix merely returns its locals. -/
theorem body_factor (ap0 ap1 : Points) (extra : Array K 2#usize)
    (iter : core.ops.range.Range Usize) (weights : Points) :
    new.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights = (do
      let (entry,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match entry with
      | none => .ok (.done weights)
      | some side =>
        let q ← Array.index_usize extra side
        let data ← prepare ap0 ap1 q
        if side=0#usize then
          let result ← side0 data weights
          .ok (.cont (iter1,result))
        else
          let result ← side1 ap1 data weights
          .ok (.cont (iter1,result))) := by
  unfold new.factored_s2_libra_weights_loop.body prepare side0 side1
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

#print axioms body_factor
end AspisR1.CuSavingsLibraSourceFactored
