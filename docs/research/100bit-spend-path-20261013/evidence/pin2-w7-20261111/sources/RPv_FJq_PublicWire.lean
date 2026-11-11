import RPv_FJq_PublicNative
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): STATEMENT CHANGE in the public-model side only:
`FIw_PublicModel.ofPublic` now takes the PIN2 `PIN2P.SemanticPublic` (W3c), so it is applied
to `PIN2W11_PublicCopy.nativePIN2` (release `FJa_PublicCopy.native` plus the PIN2
`destination`) of the same preparation public.  The model therefore also carries pool,
deployment domain and the withdrawal destination, matching W3a's wire parse.  Premises and
proof text unchanged (`FJq_PublicNative.value` restated the same way). -/
noncomputable section
namespace AspisR1.FJq_PublicWire
open FIz_ConcretePack (embed)
theorem value (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (wire : SemanticPublicWire.Wire)
    (same : PublicSourceRaw.toWire (AspisR1TerminalDecoder.PublicBinding.projectRaw s)=some wire) :
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (PIN2W11_PublicCopy.nativePIN2
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)))=
      SpendDataMap.mapPublic ExactBaseProjection.embed (SemanticPublicWire.toPublic wire) := by
  unfold PublicSourceRaw.toWire at same
  split at same
  · obtain rfl:=Option.some.inj same
    rw [FJq_PublicNative.value]
    exact (FJq_PublicModel.mapped _ _).symm
  · cases same
#print axioms value
end AspisR1.FJq_PublicWire
end
