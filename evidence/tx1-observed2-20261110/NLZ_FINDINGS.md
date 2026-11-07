# Findings

NLZ-F1: K001 stopped before Kani verification because the own configuration omitted PATH for rustc. Frozen graph check passed, post-run lock unchanged. Corrected to predecessor PATH and optimized flags at K003; same harness name. This is an own-input repair under local-lean11, not a shared-infrastructure failure or a renamed verdict.

L003/L007 syntax errors in the new resource carrier are retained; no timeout or memory kill, no limit raised.

K003 codegen rejected the own parse oracle lifetime binder (0 early-bound vs 1 required). Fixed to the frozen signature's early-bound lifetime (`a:a`) as in the predecessor. No verification ran; no verdict or harness rename.

NLZ-F2: K007 actual-parent combined begin invariant timed out at90s (95.017s scope,1979688KiB,swap0). Shape retired. The local batch controller was stopped before queued larger shapes; submitted K008 control is collected normally, never resubmitted. Replacement will split Prefix metadata, selected byte and transcript state into independent windows. No timeout/cap increase.

Replacement of K007: complete original-window metadata and transcript state are split; payload composition requires a distinct native whole-input byte frame at arbitrary global index and the Lean View/frame law. No pointer-only payload conclusion. Historical K005/006 used Transfer only; final Public coverage must include Withdrawal.

L020/L025: symbolic offset-consecutiveness tactic did not normalize the piecewise Nat arithmetic; within bounds succeeded. Replacement L026 isolates the tiny26-row partition; no limit change, no generated recurrence reduction.

NLZ-F3: the initial own137/087 projection schemas required an input View for ALL heaps, which is unsatisfiable at the empty heap. No row root used them. Corrected schemas make the physical window an explicit argument and require View/extent as an own-input admission premise; they are still weak drafts, not full packets. The original statements remain in L004/L005 snapshots; L027/L028 record the corrected source. NLZ_AdmissionCorrection.no_view_empty formalizes the counterexample. No new trust item or metric.

NLZ-F4: K025 success roots window timed out90s (94.147s scope,1472296KiB,swap0). Retired combined earlier-argument+return shape. L031 changes the oracle instrumentation to isolate the LAST return stretch, using previous argument windows separately; no frozen parent body change. K026 retries the SAME success_00_cut name with the changed shape. z/transcript fields are grouped; K040 is an independent nonzero-claims diagnostic. No cap or timeout increase.

NLZ-F5: K026 final-return roots failed an assertion-library memcmp64 unwinding check at40, not a frozen-function mismatch. L032 selects an arbitrary root byte, with no unwind/cap/timeout increase. Root field extensionality is a separate Lean obligation. Remaining controls corrupt the oracle's returned record relative to its logged reply (y), rather than invert the caller assertion. Earlier inversion controls do NOT discharge the full(y) corruption-control requirement. K040 is now the grouped z/transcript corrupted-reply control; the planned separate nonzero diagnostic is unrun.
