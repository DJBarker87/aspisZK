import SCH_ChildUpdate
import SCH_SdkPure
set_option autoImplicit false
namespace AspisR1.SCH_SecondPure
open Aeneas Aeneas.Std Result

theorem full_range (original children : AdapterRw.Ops) :
    AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice (SCH_ChildUpdate.update original children) =
      AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice original := rfl

theorem option_eq (original children : AdapterRw.Ops) {A : Type} (eq : core.cmp.PartialEq A A) :
    AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption (SCH_ChildUpdate.update original children) eq =
      AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption original eq := rfl

theorem readonly (original children : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_account (SCH_ChildUpdate.update original children) =
      AdapterRw.r1_pool_adapter.owned.require_readonly_account original := rfl

#print axioms full_range
#print axioms option_eq
#print axioms readonly
end AspisR1.SCH_SecondPure
