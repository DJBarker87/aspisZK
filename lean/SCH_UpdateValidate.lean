import SCH_UpdateAuthenticate
set_option autoImplicit false
namespace AspisR1.SCH_UpdateValidate
open SCH_ChildUpdate

theorem same (o k : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.validate_asq8 (update o k) =
      AdapterRw.r1_pool_adapter.owned.validate_asq8 o := by
  unfold AdapterRw.r1_pool_adapter.owned.validate_asq8
  simp only [SCH_UpdateAuthenticate.same,SCH_UpdatePure.data]
  simp only [update]

#print axioms same
end AspisR1.SCH_UpdateValidate
