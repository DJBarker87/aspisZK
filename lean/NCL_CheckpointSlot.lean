import S2W_D189Wrappers
set_option autoImplicit false
namespace AspisR1.NCL_CheckpointSlot
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Scalar function for adapter op12. The frozen native checkpoint_size gate
checks all three Variant cases against these values (K005/K006). Selecting this
slot does not instantiate the remaining adapter/native extraction boundary. -/
def value : aspis_r1_cost_probe.transport.Variant → Result Usize
  | .S1 => ok 4840#usize
  | .S2 => ok 1768#usize
  | .D => ok 1768#usize

def install (ops : Ops) : Ops := {ops with op12:=value}

theorem s1 : value .S1=ok 4840#usize := rfl
theorem s2 : value .S2=ok 1768#usize := rfl
theorem d : value .D=ok 1768#usize := rfl

theorem installed (ops : Ops) (variant : aspis_r1_cost_probe.transport.Variant) :
    (install ops).op12 variant=value variant := rfl

#print axioms s1
#print axioms s2
#print axioms d
#print axioms installed
end AspisR1.NCL_CheckpointSlot
