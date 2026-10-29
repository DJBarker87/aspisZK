import R1Z.PV_RunJoin_NativeResidual62
import R1Z.PV_RunJoin_AllocatorWorld63
import PV_B3P_Install132
/-! Adopted CONFIRM installations. V228 is the selected structural source/value
packet, all3803 ordered cells, exact capacity/source predicates, original carrier
and261 frames. V183 is world-indexed, with explicit metadata/error encoding;
public-size allocation failure remains rdea-1. No qualification is an axiom. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeResidual63
open Aeneas Aeneas.Std Result ProverRwFull
abbrev types := PV_RunJoin_NativeResidual62.types
abbrev Heap := PV_RunJoin_WeightInstalled46.Heap
abbrev Box := PV_RunJoin_WeightInstalled46.Box

def residual {S F : Type} (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) : @ExternalFuns (types base) :=
  @PV_RunJoin_AllocatorWorld63.at (types base) S F runtime
    (PV_B3P_Install132.selected (types base) (PV_RunJoin_NativeResidual62.residual base ops)) world

def opsNative {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) : @ExternalFuns (types base) :=
  PV_RunJoin_WeightInstalled46.selected (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world)

#print axioms types
#print axioms residual
#print axioms opsNative
end R1Z.PV_RunJoin_NativeResidual63
