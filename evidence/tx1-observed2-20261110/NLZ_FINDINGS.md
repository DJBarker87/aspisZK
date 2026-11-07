# Findings

NLZ-F1: K001 stopped before Kani verification because the own configuration omitted PATH for rustc. Frozen graph check passed, post-run lock unchanged. Corrected to predecessor PATH and optimized flags at K003; same harness name. This is an own-input repair under local-lean11, not a shared-infrastructure failure or a renamed verdict.

L003/L007 syntax errors in the new resource carrier are retained; no timeout or memory kill, no limit raised.

K003 codegen rejected the own parse oracle lifetime binder (0 early-bound vs 1 required). Fixed to the frozen signature's early-bound lifetime (`a:a`) as in the predecessor. No verification ran; no verdict or harness rename.

NLZ-F2: K007 actual-parent combined begin invariant timed out at90s (95.017s scope,1979688KiB,swap0). Shape retired. The local batch controller was stopped before queued larger shapes; submitted K008 control is collected normally, never resubmitted. Replacement will split Prefix metadata, selected byte and transcript state into independent windows. No timeout/cap increase.

Replacement of K007: complete original-window metadata and transcript state are split; payload composition requires a distinct native whole-input byte frame at arbitrary global index and the Lean View/frame law. No pointer-only payload conclusion. Historical K005/006 used Transfer only; final Public coverage must include Withdrawal.
