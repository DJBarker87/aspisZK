import NMX_Program
set_option autoImplicit false
noncomputable section
namespace NMX_FullChildren
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_Program
/-- Native217 packet at every original slice. In particular the parent does
not pre-assume768: the child must cover malformed lengths as well. Equality is
of the entire boxed Result/frame/events OR stopped prefix. -/
def RowSpec_217 {W E : Type} (native model : Handler W E) : Prop :=
 ∀ bytes before, native (.lane bytes) before = model (.lane bytes) before
/-- Native234 packet at every original seven-argument invocation. No registry
success, immutable-policy assumption or selected PDA reply is a premise. -/
def RowSpec_234 {W E : Type} (native model : Handler W E) : Prop :=
 ∀ verifier pool masterAccount master registry entry slot before,
 native (.registry verifier pool masterAccount master registry entry slot) before =
 model (.registry verifier pool masterAccount master registry entry slot) before
/-- Precisely the CLOSED/runtime/std command cases. Native instantiation must
DISCHARGE these, never retain this dictionary as a candidate-root premise. -/
def IsOpen {B : Type} : Command B → Prop
 | .lane _ => True
 | .registry _ _ _ _ _ _ _ => True
 | _ => False

def ClosedPackets {W E : Type} (native model : Handler W E) : Prop :=
 ∀ {B : Type} (cmd : Command B) before, ¬ IsOpen cmd → native cmd before = model cmd before
end NMX_FullChildren
end
