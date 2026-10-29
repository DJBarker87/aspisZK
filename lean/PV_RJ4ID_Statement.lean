import R1Z.PV_RJDec_V047Native
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4ID_Statement
open R0Z.ZkStatement
local notation "K" => PrivacyR1AcctBasis.K

/-- An actual deployed statement identification must retain transfer-13's
index and the actual commitment handle. These are necessary conditions only. -/
theorem required_fields {CH : Type} (actual : Statement K CH) (native_handle : CH)
    (identified : actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle) :
    actual.1.nextPairIndex = 13 ∧ actual.2 = native_handle := by
  constructor
  · rw [identified]
    exact AspisR1.PV_2TNV_PublicEncoding.statement_index native_handle
  · exact congrArg Prod.snd identified

/-- A live statement at any other pair index cannot be replaced by the
transfer-13 fixture, even when its handle is retained. -/
theorem other_index {CH : Type} (actual : Statement K CH) (native_handle : CH)
    (different : actual.1.nextPairIndex ≠ 13) :
    actual ≠ AspisR1.PV_2TNV_PublicEncoding.x native_handle := by
  intro identified
  exact different (required_fields actual native_handle identified).1

/-- The existing native consumer is unchanged; this is the exact conditional
interface, not a proof of identification at the deployed caller. -/
theorem consume {CH : Type} (actual : Statement K CH) (native_handle : CH)
    (identified : actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle) :
    ∃ w : PV_RJDec_V047.H.Instance, PV_RJDec_V047.H.public w = actual.1 :=
  PV_RJDec_V047Native.consume actual native_handle identified

#print axioms required_fields
#print axioms other_index
#print axioms consume
end R1Z.PV_RJ4ID_Statement
