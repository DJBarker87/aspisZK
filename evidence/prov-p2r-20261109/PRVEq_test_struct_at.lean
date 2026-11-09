import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace Gt
structure S where
  «at» : Std.Usize
  data : Std.Usize
end Gt
namespace Fr
structure S where
  «at» : Std.Usize
  data : Std.Usize
end Fr
set_option maxHeartbeats 200000 in
def PRVEq.T.S.equiv : Fr.S ≃ Gt.S where
  toFun x := { «at» := x.«at», data := x.data }
  invFun y := { «at» := y.«at», data := y.data }
  left_inv x := by
    first | (trace "PRV-S1 PRVEq.T.S"; cases x; rfl) | (trace "PRV-S2 PRVEq.T.S"; cases x; simp)
  right_inv y := by
    first | (trace "PRV-S1 PRVEq.T.S"; cases y; rfl) | (trace "PRV-S2 PRVEq.T.S"; cases y; simp)
#print axioms PRVEq.T.S.equiv

