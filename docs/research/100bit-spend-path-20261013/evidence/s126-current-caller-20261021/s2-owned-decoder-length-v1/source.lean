import S2OwnedSourceInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SourceInstallation

/-- TOTAL wrong-length rejection by the actual retained decoder. No inner
parser/validator or honest-input premise, and no bounded input-size premise. -/
theorem actual_wrong_length (bytes : Slice U8) (h : bytes.val.length ≠ 1880) :
    AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes =
      ok (.Err AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  unfold AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
  rw [AspisR1TerminalDecoder.DecoderSuccess.statement_bytes]
  have hn : Slice.len bytes ≠ 1880#usize := by
    intro he
    exact h (congrArg UScalar.val he)
  simp only [bind_tc_ok, bne_iff_ne, hn, if_true]

/-- The installed fresh full-error decoder has exactly the same early reject.
This is the concrete length contract usable at an SDK modular decoder cut. -/
theorem installed_wrong_length (bytes : Slice U8) (h : bytes.val.length ≠ 1880) :
    actualDecoder bytes = ok (.Err
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  unfold actualDecoder
  rw [actual_wrong_length bytes h]
  rfl

theorem installed_success_length (bytes : Slice U8) (statement : Reachability.Statement)
    (h : actualDecoder bytes = ok (.Ok statement)) : bytes.val.length = 1880 := by
  obtain ⟨decoded,hd,_⟩ := decoder_success bytes statement h
  exact (AspisR1TerminalDecoder.DecoderSuccess.decode_success bytes decoded hd).2.1

#print axioms actual_wrong_length
#print axioms installed_wrong_length
#print axioms installed_success_length
end AspisS2OwnedStage1.SourceInstallation
