import R1Z.PV_RJDec_ParserR20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_TerminalGuard
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder PV_W_TypedEffects
variable [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
theorem failure (bytes : Slice U8) (error : Aeneas.Std.Error)
    (first : pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = .fail error) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR20.program bytes) = .fail error := by
  rw [PV_RJDec_ParserR20.source]
  simp only [pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1,first,bind_tc_fail]
#print axioms failure
theorem divergence (bytes : Slice U8)
    (first : pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = .div) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR20.program bytes) = .div := by
  rw [PV_RJDec_ParserR20.source]
  simp only [pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1,first,bind_tc_div]
#print axioms divergence
theorem wrong_length (bytes : Slice U8) (expected : Usize)
    (first : pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = .ok expected)
    (wrong : (Slice.len bytes != expected) = true) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR20.program bytes) =
      .ok (.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  rw [PV_RJDec_ParserR20.source]
  simp only [pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1,first,bind_tc_ok,wrong,Bool.true_eq,↓reduceIte]
#print axioms wrong_length
end R1Z.PV_RJDec_TerminalGuard
