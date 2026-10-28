from pathlib import Path
E=Path(__file__).resolve().parent;D=Path('lean/NCP_HelperExtracted');D.mkdir(exist_ok=True)
old='pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1';new='pool_v1.pair_terminal.NCP_PoolV1PairVerifierTransportErrorV1'
for n in ['Types.lean','Funs.lean']:
 raw=(E/'NCP_helpers_extracted/NCP_HelperExtracted'/n).read_text();s=raw.replace(old,new);assert s.replace(new,old)==raw;(D/n).write_text(s)
(D/'FunsExternal.lean').write_text('''import AspisR1TerminalDecoder.Funs
import NCP_HelperExtracted.Types
namespace NCP_HelperExtracted
open Aeneas Aeneas.Std Result
/-- Reuse the coherent cohort's extracted generic map_err body; no new axiom. -/
abbrev core.result.Result.map_err {T E F O : Type}
    (ops : core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
    Result (core.result.Result T F) :=
  AspisR1TerminalDecoder.core.result.Result.map_err ops self op
end NCP_HelperExtracted
''')
