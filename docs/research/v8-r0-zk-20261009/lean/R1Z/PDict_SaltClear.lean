import R1Z.PDict_Array32
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_SaltClear
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_Publication.native

/-- Value effect of actual volatile whole-cell overwrite. The P6 native
contract checks all256input bits and the disjoint before/after frame.
This field is not an order/exactly-once/fence/whole-Drop theorem. -/
def zero : Array U8 32#usize := Array.make 32#usize [
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_Array32.selected base ops with op238 := fun _ => .ok zero }

theorem op238_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (cell : Array U8 32#usize) :
    (selected base ops).op238 cell = .ok zero := rfl

#print axioms op238_installed
end R1Z.PDict_SaltClear
