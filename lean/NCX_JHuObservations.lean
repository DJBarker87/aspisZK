import NCX_FixtureObservations
set_option autoImplicit false
namespace NCX_JHuObservations
open Aeneas Aeneas.Std Result AspisR1

/-- The two dictionaries update disjoint slots. -/
theorem commute (base : AdapterRw.Ops) :
    NCV_Install.install (NCX_Install.install base)=NCX_Install.install (NCV_Install.install base) := rfl

theorem registry (base : AdapterRw.Ops) :
    (JHd_ReferenceSlots.install (NCV_Install.install (NCX_Install.install base))).op33
      JHb_DataRegistry.value=ok (.Ok JHj_RegistryValue.registry) :=
  NCX_FixtureObservations.registry

theorem entry (base : AdapterRw.Ops) :
    (JHd_ReferenceSlots.install (NCV_Install.install (NCX_Install.install base))).op34
      JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry) :=
  NCX_FixtureObservations.entry

/-- Preserve the PDA runtime slot and the coherent cohort's digest/error slots. -/
theorem runtime_retained (base : AdapterRw.Ops) :
    (NCX_Install.install base).op38=base.op38 ∧
    (NCX_Install.install base).op43=base.op43 ∧
    (NCX_Install.install base).op44=base.op44 := ⟨rfl,rfl,rfl⟩

theorem ncv_retained (base : AdapterRw.Ops) :
    (NCX_Install.install (NCV_Install.install base)).op48=NCV_Install.op48 ∧
    (NCX_Install.install (NCV_Install.install base)).op49=NCV_Install.op49 ∧
    (NCX_Install.install (NCV_Install.install base)).op50=NCV_Install.op50 := ⟨rfl,rfl,rfl⟩
#print axioms commute
#print axioms registry
#print axioms entry
#print axioms runtime_retained
#print axioms ncv_retained
end NCX_JHuObservations
