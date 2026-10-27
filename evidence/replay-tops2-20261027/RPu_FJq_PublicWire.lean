import RPu_FJq_PublicNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PublicWire
open FIz_ConcretePack (embed)
theorem value (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (wire : SemanticPublicWire.Wire)
    (same : PublicSourceRaw.toWire (AspisR1TerminalDecoder.PublicBinding.projectRaw s)=some wire) :
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native
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
