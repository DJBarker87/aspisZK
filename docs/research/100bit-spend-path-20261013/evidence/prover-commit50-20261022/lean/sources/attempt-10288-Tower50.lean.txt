import AspisR1ProducerRelease47.SparseScan50
import AspisR1ProducerRelease47.SparseSum50
import AspisR1ProducerRelease47.Sparse50
import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.Prepared50
import AspisR1ProducerRelease47.Run50
import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Reconstruction49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def tower50.cm_i (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.neg x.b
  ok { a := m, b := x.a }

def tower50.mul
  (x : field.QM31) (coordinate : Std.U8) : Result field.QM31 := do
  massert ((coordinate = 0#u8) || ((coordinate = 1#u8) || ((coordinate = 2#u8)
    || (coordinate = 3#u8))))
  if coordinate = 0#u8
  then ok x
  else
    if coordinate = 1#u8
    then
      let c ← tower50.cm_i x.c0
      let c1 ← tower50.cm_i x.c1
      ok { c0 := c, c1 }
    else
      if coordinate = 2#u8
      then let c ← reconstruction.mul_r x.c1
           ok { c0 := c, c1 := x.c0 }
      else
        let c ← reconstruction.mul_r x.c1
        let c1 ← tower50.cm_i c
        let c2 ← tower50.cm_i x.c0
        ok { c0 := c1, c1 := c2 }

end AspisR1ProducerRelease47
