# Process notes

Applied source revision is recorded in APPLIED.json. The pinned tool paths and
hashes, original outputs and capped receipts are retained alongside this note.
The preflight-enabled applied extraction is independent of the older private
no-preflight diagnostics. No pinned extractor or shared launcher was edited.

Lean uses the existing Env-J run2.py driver in our capped scope, with its
unmodified environment copied into this job and read-only links to shared
objects. All new PV_Op223 sources and compiled objects are private to this job.
No shared Env-J source is written. Companion files were added to the private
object-link overlay after focused import failures (43301/43302); those are
charged attempts, not proof successes. The changed dependency environment is
the reason for the subsequent compile. The shared object sources are not
replaced or repaired.

43300 was an uncharged reservation refusal. The first retry (43301) occurred
112 seconds after it, earlier than the required 180 seconds; this was an
orchestration error. Subsequent reservation retries use three explicit
60-second cooldown intervals and fresh IDs. No resource barrier was bypassed
and no caps were raised. IDs are never reused. Kani budget is zero.
