import R1Z.ProverRwSuccessWideSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessPointsSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwDictionaryTower
abbrev field.QM31 := Q
abbrev field.QM31.mul := qMul
abbrev field.QM31.add := qAdd
abbrev field.QM31.sub := qSub
def field.QM31.ONE : Q := fromQ AspisR1ProducerRelease47.field.QM31.ONE
def state_only_prefix.state_only_statement_points_loop.body
  (z : Array field.QM31 10#usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (successor : Array field.QM31 10#usize) (carry : field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Array field.QM31 10#usize) × field.QM31) (Array field.QM31
    10#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done successor)
  | some coordinate =>
    let bit ← Array.index_usize z coordinate
    let bit_and_carry ← field.QM31.mul bit carry
    let q ← field.QM31.add bit carry
    let q1 ← field.QM31.add bit_and_carry bit_and_carry
    let q2 ← field.QM31.sub q q1
    let a ← Array.update successor coordinate q2
    ok (cont (iter1, a, bit_and_carry))

def state_only_prefix.state_only_statement_points_loop
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (z : Array field.QM31 10#usize) (successor : Array field.QM31 10#usize)
  (carry : field.QM31) :
  Result (Array field.QM31 10#usize)
  := do
  loop
    (fun (iter1, successor1, carry1) =>
      state_only_prefix.state_only_statement_points_loop.body z iter1
      successor1 carry1)
    (iter, successor, carry)

def state_only_prefix.state_only_statement_points
  (z : Array field.QM31 10#usize) :
  Result (Array (Array field.QM31 10#usize) 3#usize)
  := do
  let s ← lift (Array.to_slice z)
  let i := Slice.len s
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 0#usize, «end» := i }
  let successor ←
    state_only_prefix.state_only_statement_points_loop iter z z field.QM31.ONE
  let q ← Array.index_usize z 7#usize
  let q1 ← field.QM31.sub field.QM31.ONE q
  let absorption ← Array.update z 7#usize q1
  let q2 ← Array.index_usize absorption 6#usize
  let q3 ← field.QM31.sub field.QM31.ONE q2
  let absorption1 ← Array.update absorption 6#usize q3
  ok (Array.make 3#usize [ z, successor, absorption1 ])

def state_only_prefix.r0.statement_points
  (alpha : Array field.QM31 10#usize) :
  Result (Array (Array field.QM31 10#usize) 3#usize)
  := do
  state_only_prefix.state_only_statement_points alpha
end R1Z.ProverRwSuccessPointsSource
