import AspisR1TerminalDecoder.Funs
import NCP_HelperExtracted.Types
namespace NCP_HelperExtracted
open Aeneas Aeneas.Std Result
/-- Reuse the coherent cohort's extracted generic map_err body; no new axiom. -/
abbrev core.result.Result.map_err {T E F O : Type}
    (ops : core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
    Result (core.result.Result T F) :=
  AspisR1TerminalDecoder.core.result.Result.map_err ops self op
end NCP_HelperExtracted
