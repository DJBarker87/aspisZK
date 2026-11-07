import NMT_345Validator
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
open NFY_NBG_PaymentChecks
/-- Extract only the small canonicality guard, never the encoded byte image. -/
theorem payment_common_canonical (c : C) (good : common c = .Ok ()) :
 canonical c.anchor_root = true ∧ canonical c.nullifier = true := by
 unfold common at good
 split at good
 · cases good
 · split at good
   · cases good
   · cases ha : canonical c.anchor_root <;> cases hn : canonical c.nullifier <;>
      simp_all
#print axioms payment_common_canonical
end NMT_345
