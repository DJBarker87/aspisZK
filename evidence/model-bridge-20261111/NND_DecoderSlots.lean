import NFY_Part059
import NJQ_Canonical
import NCX_Install
import NKF_MasterBox
import NKF_CheckpointBox
import NIS_ActiveSlots
import NHY_RegistrySlots
set_option autoImplicit false
noncomputable section
namespace NND_DecoderSlots
open Aeneas Aeneas.Std Result AdapterRw
/-- Concrete CLOSED decoder/predicate carriers. The native217 decoder is a
separate OPEN installation; this is not the final exhibited missing instance. -/
def install (base : Ops) : Ops :=
 {NIJ_ActiveSlots.install (NHY_RegistrySlots.install base) with
  op23 := AspisR1.NFY_JHd_RequestNative.decode
  op31 := NJQ_Canonical.registry
  op32 := NJQ_Canonical.entry
  op33 := NCX_Install.op33
  op34 := NCX_Install.op34
  op48 := NKF_MasterBox.reference
  op49 := NKF_CheckpointBox.reference}

theorem selected (base : Ops) :
 (install base).op23 = AspisR1.NFY_JHd_RequestNative.decode ∧
 (install base).op31 = NJQ_Canonical.registry ∧
 (install base).op32 = NJQ_Canonical.entry ∧
 (install base).op33 = NCX_Install.op33 ∧
 (install base).op34 = NCX_Install.op34 ∧
 (install base).op48 = NKF_MasterBox.reference ∧
 (install base).op49 = NKF_CheckpointBox.reference := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active (base : Ops) : (install base).op29 = NIJ_ActiveSlots.op29 ∧
 (install base).op30 = NIJ_ActiveSlots.op30 := ⟨rfl,rfl⟩

theorem flags (base : Ops) : (install base).op25 = (NHY_RegistrySlots.install base).op25 ∧
 (install base).op26 = (NHY_RegistrySlots.install base).op26 ∧
 (install base).op27 = (NHY_RegistrySlots.install base).op27 ∧
 (install base).op28 = (NHY_RegistrySlots.install base).op28 := ⟨rfl,rfl,rfl,rfl⟩

theorem untouched (base : Ops) : @(install base).op10 = @base.op10 ∧
 @(install base).op11 = @base.op11 ∧ (install base).op43 = base.op43 ∧
 (install base).op44 = base.op44 ∧ (install base).op50 = base.op50 := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms selected
#print axioms active
#print axioms flags
#print axioms untouched
end NND_DecoderSlots
