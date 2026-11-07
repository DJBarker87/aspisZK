import NMT_345DataCloneSemantics
set_option autoImplicit false
namespace NMT_345CloneSemantics
open RSL
/-- An exact getter-model difference on an own argument. The actual String
clone bridge is source/library work, not assumed as a theorem premise. -/
theorem deferred_string_models_differ (a : OwnedAccount) (msg : String)
 (deferred : a.bytes = .error (.borshIoError msg)) (nonempty : msg.isEmpty = false) :
 getData a ≠ RS.ofExcept a.data := by
 intro same
 have abort := data_string_abort a msg deferred nonempty env0
 rw [same] at abort
 exact pure_data_no_abort a env0 abort
#print axioms deferred_string_models_differ
end NMT_345CloneSemantics
