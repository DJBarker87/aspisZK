import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJH_Observer
open Aeneas Aeneas.Std Result
/-- Canonical emitted frozen observer body (AdapterRwModel.lean:648).
NIV_L022 does not actually emit this declaration; provenance gap is disclosed.
No Kani assertion about a function pointer is used. -/
theorem emitted (ops : AdapterRw.Ops) :
    AdapterRw.observer ops = ok none := rfl
#print axioms emitted
end AspisR1.NJH_Observer
