import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Vary only fields absent from the caller dependency closure. -/
@[reducible] def replace (ops other : ExternalFuns) : ExternalFuns :=
  { ops with
    op13 := other.op13
    op16 := other.op16
    op17 := other.op17
    op18 := other.op18
    op85 := other.op85
    op124 := other.op124
    op238 := other.op238 }
end R1Z.PDict_ReachErase
