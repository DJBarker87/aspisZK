import NNH_ValidateFission
open Aeneas Aeneas.Std Result AdapterRw
namespace NNH_ScalarOpInspect
def mulOp : Result Usize := 3#usize * 32#usize
def addOp : Result Usize := 8#usize + 96#usize
set_option pp.notation false in
set_option pp.explicit true in
#print mulOp
set_option pp.notation false in
set_option pp.explicit true in
#print addOp
#print Aeneas.Std.UScalar.tryMk
end NNH_ScalarOpInspect
