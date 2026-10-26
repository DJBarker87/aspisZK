import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
@[reducible] def replace (ops other : ExternalFuns) : ExternalFuns :=
  { ops with op85 := other.op85 }
end R1Z.PDict_FmtErase
