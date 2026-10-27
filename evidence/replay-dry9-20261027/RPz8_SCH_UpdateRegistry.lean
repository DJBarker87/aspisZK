import RPz8_SCH_UpdatePure
import RPz8_SCH_SecondPure
set_option autoImplicit false
namespace AspisR1.SCH_UpdateRegistry
open SCH_ChildUpdate

/-- All registry checks retain the original operations; only verifier calls
are interpreted per oracle. This is a complete error-preserving equality. -/
theorem same (o k : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry (update o k) =
      AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry o := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  simp only [SCH_UpdatePure.data,SCH_UpdatePure.pubkey,SCH_SecondPure.readonly]
  simp only [update]

#print axioms same
end AspisR1.SCH_UpdateRegistry
