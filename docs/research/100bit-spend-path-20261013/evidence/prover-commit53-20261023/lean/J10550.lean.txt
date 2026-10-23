import AspisR1ProducerRelease47.Weights53
import AspisR1ProducerRelease47.Weights49
import AspisR1ProducerRelease47.PointRows49
import AspisR1ProducerRelease47.Points49
import AspisR1ProducerRelease47.Stored49
import AspisR1ProducerRelease47.KernelCallers49
import R1Z.ProverCommitInactiveSource49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def weights_material53.fill
  (st : (Std.U8 × (Array (Array (Array field.QM31 4#usize) 5#usize) 5#usize)
  × (Array (Array field.QM31 10#usize) 3#usize) × (Array field.QM31
  2#usize))) (kp : Array field.wide_exact.WideExact 7#usize)
  (out : Array field.wide_exact.WideExact 1024#usize) (j : Std.Usize)
  (left : Std.U16) :
  Result (Array field.wide_exact.WideExact 1024#usize)
  := do
  if left = 0#u16
  then ok out
  else
    let row ← weights53.row st j
    let we ← Array.index_usize out j
    let we1 ← owned.cell kp row 0#usize 7#u8 we
    let out1 ← Array.update out j we1
    let i ← lift (Std.Usize.wrapping_add j 1#usize)
    let i1 ← lift (Std.U16.wrapping_sub left 1#u16)
    weights_material53.fill st kp out1 i i1
partial_fixpoint

def weights_material53.all
  (st : (Std.U8 × (Array (Array (Array field.QM31 4#usize) 5#usize) 5#usize)
  × (Array (Array field.QM31 10#usize) 3#usize) × (Array field.QM31
  2#usize))) (kp : Array field.wide_exact.WideExact 7#usize) :
  Result (Array field.wide_exact.WideExact 1024#usize)
  := do
  let a := Array.repeat 1024#usize field.wide_exact.WideExact.ZERO
  weights_material53.fill st kp a 0#usize 1024#u16

end AspisR1ProducerRelease47
