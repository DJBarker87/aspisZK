import FJq_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PublicNative
/-- The installed source public model reads the literal raw projection of this
same returned statement, for either transfer or withdrawal. -/
theorem value (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    FIw_PublicModel.ofPublic (FJa_PublicCopy.native
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))=
      FJq_PublicModel.model (AspisR1TerminalDecoder.PublicBinding.projectRaw s) := by
  cases s <;> rfl
#print axioms value
end AspisR1.FJq_PublicNative
end
