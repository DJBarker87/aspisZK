# Excluded attempts and corrections

- K001: own scratch allocator_api configuration missing; corrected before later native scopes.
- K030:32-byte append transition timed out; replaced by the exact one-byte KMX step plus Lean byte/frame composition K036..039. Not rerun unchanged.
- K066: large unsafe arbitrary-prefix Vec::resize prestate timed out. No credit.
- K096: large-prestate Vec::push u8 timed out. The original queue incorrectly treated exit1 as an expected verification failure and submitted K097's negative control and K098's QM31 family member before it was stopped. K097 failed quickly; K098 timed out. All three are excluded. The queue is now stopped on timeout diagnostics, not merely process exit code. This was an own-script mistake, not host infrastructure failure, and is not presented as an unchanged-shape pass.
- A later attempted K098 identifier collided with its already completed receipt; the runner rejected it before a launch. Preserve NGC_K098-PRELAUNCH_COLLISION.log. There was no resubmission.
- K099: physical two-cell unsafe arbitrary prestate also timed out; corrected queue stopped before its control. Final split removes unsafe provenance and dynamic prefix: ordinary owned Vec, actual reservation, arbitrary old/value, fixed physical1→2 actual resize and observed old/written cell. Original resize_step_* harness names retained. K100/031,032/033,034/035,067/068 pass/fail as required. General32768 length/value is a Lean/Std interpretation claim, never inferred from the two-cell probe alone.
- L001/L003/L005 and failed draft elaborations L021/L028/L044/L047/L054/L055: setup/path/syntax/lemma errors corrected in focused new-module work; failed outputs and any sorryAx prints excluded. Final corresponding modules and combined raw audits are green.
- L009: own missing fixture pin before a scope launch; fixed, conservatively charged, fixtures later replayed. No host infrastructure change.
- L018:14 missing expected-import entries, zero dangling; repaired only from exact pinned source headers, then L020 passed.
- L062: host audit succeeded; own retrieval tried decoding compressed graphs as text. Recovered completed receipts read-only and added binary-safe recovery, without resubmission.
- L063: all raw proof modes passed, final scan failed on one omitted LPi_WriterValues expected-import entry; zero dangling. Exact source header pinned; focused L064 scan passed. New-prestate L068 audit/scan passed. L070 binds the final expected manifest hash explicitly in the source receipt; no unchanged proof replay.

No Kani verdict was obtained by renaming; no cap or timeout was raised. No selected pass depends on a writable static, Option<fn>, field-multiplication stub or unsupported function contract. All excluded receipts remain immutable evidence.
