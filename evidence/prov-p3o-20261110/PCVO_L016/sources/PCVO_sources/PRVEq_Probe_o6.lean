import Aeneas
import NHL_DriverModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller
set_option autoImplicit false
noncomputable section
section
variable (base expected : AspisR1CurrentCaller.Ops) (reserved : Bool)
example : (NHL_DriverModel.preparedOps base expected reserved).op12 = ok 16#usize := rfl
example : (NHL_DriverModel.preparedOps base expected reserved).op13 = ok 7015#usize := rfl
example : (NHL_DriverModel.preparedOps base expected reserved).op14 = ok 464#usize := rfl
example : (NHL_DriverModel.preparedOps base expected reserved).op15 = ok 13831#usize := rfl
example : (NHL_DriverModel.preparedOps base expected reserved).op21 = ok 7527#usize := rfl
example : (NHL_DriverModel.preparedOps base expected reserved).op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse := rfl
example : (NHL_DriverModel.txOps base expected reserved).op12 = ok 16#usize := rfl
example : (NHL_DriverModel.txOps base expected reserved).op13 = ok 7015#usize := rfl
example : (NHL_DriverModel.txOps base expected reserved).op14 = ok 464#usize := rfl
example : (NHL_DriverModel.txOps base expected reserved).op15 = ok 13831#usize := rfl
example : (NHL_DriverModel.txOps base expected reserved).op21 = ok 7527#usize := rfl
example : (NHL_DriverModel.txOps base expected reserved).op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse := rfl
end
