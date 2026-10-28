import NCX_FixtureCarriers
import JHd_ReferenceSlots
set_option autoImplicit false
namespace NCX_FixtureObservations
open Aeneas Aeneas.Std Result AspisR1

theorem registry : NCX_Install.op33 JHb_DataRegistry.value=ok (.Ok JHj_RegistryValue.registry) := by
  simp only [NCX_Install.op33,NCX_RegistryFixture.source,bind_tc_ok,NCX_Install.mapReturn,
    NCX_FixtureCarriers.registry]
theorem entry : NCX_Install.op34 JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry) := by
  simp only [NCX_Install.op34,NCX_EntryFixture.source,bind_tc_ok,NCX_Install.mapReturn,
    NCX_FixtureCarriers.entry]
theorem installed_registry (base : AdapterRw.Ops) :
    (JHd_ReferenceSlots.install (NCX_Install.install (NCV_Install.install base))).op33
      JHb_DataRegistry.value=ok (.Ok JHj_RegistryValue.registry) := registry
theorem installed_entry (base : AdapterRw.Ops) :
    (JHd_ReferenceSlots.install (NCX_Install.install (NCV_Install.install base))).op34
      JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry) := entry
#print axioms registry
#print axioms entry
#print axioms installed_registry
#print axioms installed_entry
end NCX_FixtureObservations
