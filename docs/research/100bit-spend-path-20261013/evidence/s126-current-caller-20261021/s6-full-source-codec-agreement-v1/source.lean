import S6FullSourceCodecV1
import S6FiveCodecStdOptionsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.Agreement
abbrev Statement := AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1

/-- Complete Result equality, including failure/divergence and ordinary errors.
The unused external template does not affect the enclosing encoder. -/
theorem encode_eq (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq)
    (statement : Statement) :
    AspisS6SourceCodec.encode statement =
      AspisS6FiveUnrolledCodec.StdOptions.encode unused statement := by
  rfl

/-- The SAME full statement carrier and arbitrary input bytes are retained. -/
theorem decode_eq (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq)
    (bytes : Slice U8) :
    AspisS6SourceCodec.decode bytes =
      AspisS6FiveUnrolledCodec.StdOptions.decode unused bytes := by
  rfl

#print axioms encode_eq
#print axioms decode_eq
end AspisS6SourceCodec.Agreement
