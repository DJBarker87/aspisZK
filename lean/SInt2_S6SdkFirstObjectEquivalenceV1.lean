import SInt2_SdkDependencyFactorV1
set_option autoImplicit false
namespace AspisS6SdkFirstObjectEquivalence
/-- The canonical complete wrapper is the original wrapper. -/
abbrev originalFirst := @AspisR1.S2W_D189Wrappers.first

theorem first_eq_original : @AspisR1.S2W_D189Wrappers.first = @originalFirst := rfl
#print axioms first_eq_original
end AspisS6SdkFirstObjectEquivalence
