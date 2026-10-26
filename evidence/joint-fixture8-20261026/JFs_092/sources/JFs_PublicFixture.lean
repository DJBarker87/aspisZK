import JFs_PublicDecode
import JFs_PublicSerialization
import JFs_SourceProjection
set_option autoImplicit false
namespace AspisR1.JFs_PublicFixture
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

/-- Joint public-input fixture. This states no native TX1/TX2 acceptance. -/
theorem inhabited :
    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 JFx_NativeBytes.publicInput=
      ok (.Ok JFs_PublicValue.value) ∧
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 JFs_PublicValue.value=ok (.Ok ()) ∧
    ∃ encoded : alloc.vec.Vec U8,
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1CurrentCaller.FirstComposition.toRetainedPublic
          (AspisS6CurrentVerifierCarrier.toPublic
            (S6N_Getters.publicValue
              (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 JFs_PublicValue.value))))=
          ok (.Ok encoded) ∧ encoded.val.length=1455 := by
  obtain ⟨encoded,serialized,contents,length⟩:=JFs_PublicSerialization.source
  refine ⟨JFs_PublicDecode.source,JFs_PublicValidation.source,encoded,?_,length⟩
  rw [JFs_SourceProjection.source]
  exact serialized

#print axioms inhabited
end AspisR1.JFs_PublicFixture
