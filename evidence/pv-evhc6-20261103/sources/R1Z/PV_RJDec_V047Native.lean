import R1Z.PV_RJDec_V047
import PV_2TNV_HeadlineFibre
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_V047Native
open R0Z.ZkStatement
local notation "K" => PrivacyR1AcctBasis.K
/-- The original transfer-13 fibre is supplied here, rather than left as a
premise. The actual native statement equality is still an explicit obligation.
No wrapper execution or FixturePdaRuntime law is consumed by this theorem. -/
theorem consume {CH : Type} (actual : Statement K CH) (native_handle : CH)
    (native_identification : actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle) :
    ∃ w : PV_RJDec_V047.H.Instance, PV_RJDec_V047.H.public w = actual.1 :=
  PV_RJDec_V047.consume (AspisR1.PV_2TNV_PublicEncoding.x native_handle) actual
    (AspisR1.PV_2TNV_HeadlineFibre.fibre native_handle) native_identification

/-- Full statement identity has two components. This criterion does not erase
or alter the native commitment handle to obtain public-component equality. -/
theorem identification_iff {CH : Type} (actual : Statement K CH) (native_handle : CH) :
    actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle ↔
    actual.1 = (AspisR1.PV_2TNV_PublicEncoding.x native_handle).1 ∧
    actual.2 = native_handle := by
  constructor
  · intro eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  · rintro ⟨public_eq,handle_eq⟩
    exact Prod.ext public_eq handle_eq
#print axioms consume
#print axioms identification_iff
end R1Z.PV_RJDec_V047Native
