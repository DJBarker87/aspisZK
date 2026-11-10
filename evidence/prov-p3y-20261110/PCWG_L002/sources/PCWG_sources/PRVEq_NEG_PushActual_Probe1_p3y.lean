import Aeneas
import PRVEq_NEG_PushActual_Funs_p3y
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
noncomputable section
#check @MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
#check @core.slice.iter.IteratorIterMut.next
#print core.slice.iter.IterMut
namespace NEG_PushActual
namespace PRVFresh_NEG_PushActual_Funs_p3y
def verifier.update_residue_row
  (row : Array Std.U64 4#usize) (power : aspis_core.field.QM31)
  (basis : aspis_core.field.M31) (flush : Bool) :
  Result (Array Std.U64 4#usize)
  := do
  let i := power.c0.a
  let i1 := power.c0.b
  let i2 := power.c1.a
  let i3 := power.c1.b
  let row1 ←
    verifier.update_residue_row_loop0 { start := 0#usize, «end» := 4#usize }
      row basis (Array.make 4#usize [ i, i1, i2, i3 ])
  if flush
  then
    let (iter, into_iter_back) ←
      MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        row1
    let (im, back) ← verifier.update_residue_row_loop1 iter (fun im1 => im1)
    let im1 := back im
    ok (into_iter_back im1)
  else ok row1
end PRVFresh_NEG_PushActual_Funs_p3y
end NEG_PushActual
