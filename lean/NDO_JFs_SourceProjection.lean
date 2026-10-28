import NDO_JFs_PublicValue
import RPz8_S6N_Installation
import ExtractedPublicPreparationBinding
set_option autoImplicit false
namespace AspisR1.JFs_SourceProjection
open Aeneas Aeneas.Std Result

theorem source : AspisR1CurrentCaller.FirstComposition.toRetainedPublic
    (AspisS6CurrentVerifierCarrier.toPublic
      (S6N_Getters.publicValue
        (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 JFs_PublicValue.value)))=
    AspisR1PublicPreparation.PreparationBinding.preparationPublic JFs_PublicValue.value := by rfl

#print axioms source
end AspisR1.JFs_SourceProjection
