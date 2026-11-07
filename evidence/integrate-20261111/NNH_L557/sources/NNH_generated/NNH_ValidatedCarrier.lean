import NNH_Libraries
set_option autoImplicit false
namespace NNH_ValidatedCarrier
open Aeneas Aeneas.Std AdapterRw NNH_Libraries

def value (a : r1_pool_adapter.ValidatedAsqa) : RSL.TX2_242.Validated L :=
 ⟨a.statement,a.proof_length.val⟩
end NNH_ValidatedCarrier
