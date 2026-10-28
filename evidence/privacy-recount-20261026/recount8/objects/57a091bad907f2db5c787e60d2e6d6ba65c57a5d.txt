import R1Z.PDict_CtConstructor
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_VolatileCell
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_CtConstructor.native
/-- Value interpretation of the uniquely borrowed volatile overwrite.
P6 association is checked at all actual mask-cell instances M31 and QM31,
for every input/replacement bit pattern and both neighboring cell frames.
This asserts no fence, temporal trace, or blanket arbitrary-Rust-T Drop law. -/
def overwrite {T : Type} (_ : core.marker.Copy T) (_value replacement : T) : Result T :=
  .ok replacement
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_CtConstructor.selected base ops with op124 := overwrite }

theorem op124_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op124 (native base) (selected base ops) = @overwrite := rfl

theorem value_replaced {T : Type} (copy : core.marker.Copy T)
    (value replacement : T) : overwrite copy value replacement = .ok replacement := rfl
#print axioms op124_installed
#print axioms value_replaced
end R1Z.PDict_VolatileCell
