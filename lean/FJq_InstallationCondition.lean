import FJq_InstallationFinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_InstallationCondition
open DrvC_Installation
/-- Exact missing installation constraint; it is NOT assumed or added to ARX. -/
theorem iff_fixed {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).boundaries.terminal=FIq_Terminal.terminal ↔
      c.boundaries.terminal=FIq_Terminal.terminal := by
  rw [FJn_InstallationBoundary.adopted]
/-- The proposed constrained configuration class is inhabited at the dictionary
level for every input seed. No joint accepted-source fixture is asserted. -/
theorem seed_exists {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    ∃ chosen : Configuration FIo_Install.W C,
      chosen.boundaries.terminal=FIq_Terminal.terminal ∧
      FIp_Install.configuration err chosen r=FIq_Install.configuration err c r :=
  ⟨FIq_Install.seed c,rfl,rfl⟩
#print axioms iff_fixed
#print axioms seed_exists
end AspisR1.FJq_InstallationCondition
end
