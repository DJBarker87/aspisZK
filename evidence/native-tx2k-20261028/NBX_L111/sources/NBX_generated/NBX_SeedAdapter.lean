import NBX_HeadlineSelection
set_option autoImplicit false
noncomputable section
namespace NBX_SeedAdapter
open Aeneas Aeneas.Std Result AspisR1
#print IDa_Deployed.seed
/-- Exact existing headline seed projection; no adapter law is assumed. -/
theorem adapter {E : Type} (m : IDa_Deployed.Uninstalled E)
    (r : NP6_StdModel.Reservation) :
    (IDa_Deployed.seed m r).adapter = m.adapter := rfl
#print axioms adapter
end NBX_SeedAdapter
end
