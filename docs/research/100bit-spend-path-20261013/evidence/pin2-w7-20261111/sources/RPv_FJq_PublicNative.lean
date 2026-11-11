import RPv_FJq_PublicModel
import PIN2W11_PublicCopy
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): `FIw_PublicModel.ofPublic` now takes the PIN2 `PIN2P.SemanticPublic`
(W3c).  STATEMENT CHANGE: the left side applies it to `PIN2W11_PublicCopy.nativePIN2` of the
preparation public (the release `FJa_PublicCopy.native` plus the PIN2 `destination`) instead of
the pre-PIN2 `FJa_PublicCopy.native`, which no longer has the argument type; the right side
`FJq_PublicModel.model (projectRaw s)` is textually unchanged (W3a's model now carries pool,
deployment domain and the withdrawal destination).  Proof: the release `rfl`, after rewriting
the probe-crate byte helper `PIN2P.bytes32` to the raw bridge's `rawBytes32` (`bytes32_eq`). -/
noncomputable section
namespace AspisR1.FJq_PublicNative
/-- The installed source public model reads the literal raw projection of this
same returned statement, for either transfer or withdrawal. -/
theorem value (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    FIw_PublicModel.ofPublic (PIN2W11_PublicCopy.nativePIN2
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))=
      FJq_PublicModel.model (AspisR1TerminalDecoder.PublicBinding.projectRaw s) := by
  have fn : PIN2P.bytes32=fun a=>(AspisR1PublicSerializer.RawBridge431.rawBytes32 a).val :=
    funext PIN2W11_PublicCopy.bytes32_eq
  cases s <;> simp only [FIw_PublicModel.ofPublic, fn] <;> rfl
#print axioms value
end AspisR1.FJq_PublicNative
end
