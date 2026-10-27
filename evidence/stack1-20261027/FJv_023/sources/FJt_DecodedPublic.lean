import F3V_Decoded
import FJq_SourceLiteralPublic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_DecodedPublic
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller

theorem value {F C : Type} (c : DrvC_Installation.Configuration F C)
    (physical : Slice U8) (semantic : Port1_Driver.Semantic)
    (success : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) physical=ok (some semantic)) :
    ∃ s : AspisR1TerminalDecoder.PublicBinding.Statement,
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        physical=ok (.Ok s) ∧
      FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic)=
        AspisR1PublicPreparation.PreparationBinding.preparationPublic s := by
  obtain ⟨statement,decoded,checked,selected⟩:=F3V_Decoded.fields (DrvC_Installation.sdk c) physical semantic success
  have source:=AspisS6CurrentCodecInstallation.decode_success physical statement decoded
  have same:=AspisS6CurrentFirstInstallation.selected_public statement
  rw [selected,bind_tc_ok] at same
  have pub:=congrArg FirstComposition.toRetainedPublic (Result.ok.inj same)
  rw [FirstComposition.retained_current_roundtrip] at pub
  exact ⟨_,source,pub⟩
#print axioms value
end AspisR1.FJt_DecodedPublic
end
