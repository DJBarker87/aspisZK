# Source assessment

Reviewed immutable ResourceRssGOv3 revision45d137dd34; no live/root/A source reads.
FinalNativeGate-function-identity JSON records per-function raw bytes and Python
AST hashes plus complete original dependency pins. Every candidate/go/identity/
inventory/policy/fixture source in FinalNativeGate_reviewed.json was compared
byte-for-byte against its own reviewed immutable revision. No unchanged full
policy regression was rerun. Four tiny raw-fixture generators reused.

Changed glue, reviewed explicitly:
- policy loader load_bundle: fixed new bundle filename; missing bundle raises,
  no Git fallback at runtime. Unused bundle() removed; digest/functions/load/
  validate_bundle unchanged. Bundle trust pins and policy bytes unchanged.
- adapter: ONLY import namespace and UNIT constant changed. visibility and
  read_only_admission complete function bytes/AST unchanged; policy evaluates
  actual snapshots itself. Changing UNIT affects the binding expectation, not
  the accounting formula or hierarchy visibility.
- observation save: fixed exclusive job packet, fsync file then directory.
  collect: raw label go maps to existing inside-scope policy phase. Both full
  snapshots/visibility/evaluate remain; no report projection or caller callback.
  digest/filepin/runtime_pins/controls/check_controls unchanged byte-for-byte.
- guard constants: BUDGET512MiB ->4GiB to monitor the actual capped workload and
  parent tree; MAX_SAMPLES8192 ->32768 covers lifecycle. This is a job-specific
  guard, not a change to the shared metadata watchdog or resource policy.
  Guard.__init__ uses raise_signal for its own notification; Guard.sample only
  changes failure-message text; Guard.finish changes descriptive kind text.
  All inherited rlimit, process identity, TGID accounting, pidfd cancellation,
  lineage/loop/start/finish logic otherwise unchanged. Sampling remains bounded
  observation; no continuous peak/child cancellation completeness proof.
- FinalNativeGate.py/inside are NEW fixed source. main functions return78
  literally, with no branch/global/argument activation. Private producer has
  no supplied job argv, manifest path, callbacks or admission truth. It calls
  concrete collect prospectively and twice inside with fresh identity/controls/
  pins; it writes a durable charge before ONE fixed Kani Popen. Actual observed
  control snapshots are saved before checking so pressure failures retain data.
  Private packet lstat checks owned private directory and rejects symlinks.

These statements concern source identity, not a runtime correctness theorem.
Existing OS/Python/tool/allocator/compiler/Kani/policy boundaries remain. Source
hashes cannot establish executed-body identity; runtime collector's mapped-
library/ELF observations are incomplete for native Kani child dependency closure.
That exact missing pin interface is recorded as null in the sealed plan and
unconditionally denies preflight. Future review must fill exact closure/pins,
not supply an expected GO truth or old1GiB marker.

No theorem or premise changed (before=after scalar RELATION/P6 SOURCE-CONTRACT).
No native semantic premise discharged. All fixed source inputs retain arbitrary
nonce32/post64/entry16/valid NonZeroI32/coordinate and real Drop/copies/scans/wipes.
Full security targets NOT ESTABLISHED. Metadata ResourceMeta1G epoch7, ordinary
MIR and older component checks are historical context only, no new identity gate.
