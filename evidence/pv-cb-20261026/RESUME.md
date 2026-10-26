# Latest checkpoint (supersedes counts below)
Lean91/100; next22892. Kani17/20 with array017 running (session73901).
No other own scope. Kani14pop failed memcmp unwind,15empty and16default passed.
012mask unwind failure,013mask180s timeout. Whole native mask relation still OPEN.
OwnedMask80, Leaves82, ReverseWrap83, Linears84, Horner85, LinearsTotal86,
HornerTotal87, LinearsEq91 green. Failed81/88/89/90 retained. Four pending modules:
OwnedMaskHornerEq, OwnedMaskFill, OwnedMaskFillTotal, OwnedMaskTotal, not yet compiled.
Fresh late-op checks205–261 and full73-op status table in FINAL-STATUS.md/json.
0 full ledger/endpoint premises removed. Continue remaining budget; no push.

# Latest checkpoint (supersedes counts below)
Lean79/100; next22880. Kani10/20, Kani11 zst running. Own scope only.
EncoderTotal22879 passed. Native small reserve010 passed. No endpoint rows removed.
Latest per-run inputs frozen in native job directories. Continue whole budget.

# Active work handoff, relaunch1

Read pv-common.txt first and its LEAD RULINGS. Task remains active; target not
established; endpoint/full ledger removals0. Never touch sibling worktrees or
ProverRw* sources; owned modules PV_CB_ only; no shipped crates/programs edits.

Budget at this handoff: Lean69/100 (IDs22800–22869 excluding22826 guard refusal),
Kani8/20. Latest69 MaskHorner passed;65 MaskFillBody passed,66 MaskFillLoop passed,67 ForwardTotal passed,68 MaskFillTotal passed. Every actual compile has numbered receipts.
Next unused Lean ID22870. ID22826 was refused67 before Lean (local edit failure);
never reuse it. No memory caps/settings were raised. A few early outer native
reservation scans were denied before3minutes; no launch bypassed a refusal.
A session timestamp guard now enforces the full wait. Latest native denial:
kani-ascii-005 pre-admission retry3 around14:56UTC; session timestamp guard records exact next time; next native scan must be
AFTER14:59:30UTC (conservative). Retry with new admission-retry4.json and redirected log.
One capped scope at a time; Lean launcher via sh, 7000 8 J (TasksMax128 accepted).
Native scopes6G/8G/swap0/Tasks64 using existing native-drop/scope.py unchanged.

Native job history:
- kani-take-001 passes u64 and Nonzero Default=37 (one invocation).
- kani-pathbuf-002 passes arbitrary Unix bytes length0..16 (deref/AsRef).
- kani-string-003 ran once after refusal; timed out180s for arbitrary valid UTF8
  byte strings length0..16. Do NOT rerun unchanged. Own timeout cgroup was gone.
- kani-join-004 passes arbitrary byte prefix/suffix lengths0..8, no stubs.
- kani-ascii-005 has NOT RUN. Pre-scan allowed, in-scope barrier refused; retry1
  pre-scan refused. This is next native gate, checks::string_ascii8.
  tools/pv-cb-20261026/proof/lib.rs is already uploaded (new std harnesses).
  Command shape retained in earlier scope receipt, choose ASCII harness.
  CARGO_PROFILE_DEV_OPT_LEVEL=3, timeout180, kissat, -j4, same caps.

Host own dir /home/dombarker/project-offloads/codex-pv-cb-20261026/.
source/ is an isolated git-archive snapshot of unchanged shipped code. source-proof/
contains cfg(kani)-only wrappers, safe owned refs, and pending M31 encoder/QM31 mask
Kani harnesses (no stubs). Profile opt3, overflow/debug assertions false for native
release arithmetic. The standalone proof/ std crate remains separate.

Important source/refinement boundaries:
- PV_CB_* WIP selectors through Borrow all compile; table ENTRIES.md. These are
  source/value interpretations, not whole native or headline closure.
- Take reference Charon/Aeneas succeeds; PV_CB_TakeExtraction matches generic
  extracted reference and preserves Default fail/div. Native gate only named
  Default instances; arbitrary native Default/Drop not established.
- Direct current encoder and mask Aeneas translations both fail Not_found in
  loop joining (InterpReduceCollapse). No backend/infrastructure repair allowed.
- Owned encoder loop ref also failed same; exact old source retained as
  aeneas-owned-encoder-001/owned-loop-reference.rs.txt (hash checked).
- Owned encoder recursion ref SUCCEEDS (charon-owned-encoder-002 and
  aeneas-owned-encoder-002). Raw generated source under owned-encoder-rec-generated.
  PV_CB_OwnedEncoder.lean changes only Types import and namespace open; field-for-
  field carrier/trait comparison pinned normalization.json. Its generated options
  are retained. Compile22854 passes; no generic native correspondence claimed.
- PV_CB_EncoderInstall (22855) installs extracted reference and eliminates old
  op79 input field; native Kani still pending, so DO NOT mark full op79 closed.
- PV_CB_EncoderCell (22857) and EncoderFill (22859) prove symbolic bounds and
  fill recurrence/totality under explicit primitive multiplication-total premise.
  They never reduce concrete512-cell arrays. Next mathematical step: basis_round
  totality/control, then encoder_fold indices and512-step symbolic recurrence.
- PV_CB_MaskSource (22829) is PREPARED only: old checked control bodies rebound to
  checked current wrapping field API, fresh current-source equality not proved.
  mask_source.py --check validates generator. Do NOT claim op117 installed.
- CurrentComplex/More/Neg/Quartic (22830/33/35/36) all pass: current machine
  arithmetic equals retained release, all u32 including noncanonical. CurrentTotal
  (22839), PreparedTotal(22840), MaskLeaves(22842), MaskLinearsFinite(22847),
  MaskLinearsTotal(22848), MaskIndices(22850), ForwardRange(22852), ForwardLoop(22853)
  pass. These are useful generic symbolic helpers; native mask correspondence open.
- Next mask step: factor generic cell (data[N], exponents[N], coefficients[27]);
  connect loop0/loop1 body to ForwardLoop.body, then apply its finite recurrence
  and static exponent/tower bounds. Root Horner reverse26 loop analogous linears.
- Owned mask safe ref is PREPARED in source-proof/owned.rs, uses loops; probably
  replace its loops with recursive owned helpers before extraction, as for encoder.
  Need native Kani proving actual = reference without stubs before closure.

Native pending checks prepared in proof/lib.rs: ASCII8, Unicode scalar, capacity16,
push_ascii8, reserve_overflow/reserve_small/reserve_zst_overflow, pop16, empty16,
default_vec,array4. Original string_path16 timeout cannot be repeated unchanged.
New source-proof checks: encoder_m31 (canonical1024 coefficients), mask_qm31
(all37 raw four-u32 words, unwind32). Actual generic op79 selected WideExact still
needs appropriate native scope/control transport; M31 gate alone is not universal.
Do not claim trial scopes prove all Default/types/allocators or L1/L2/L3.

Sibling precheck: precheck.py N [suffix] runs required multi-revision log and
separate heads plus git-show table matches. Receipts already through134 from WIP;
latest resume1 checks79 and117. Still work ascending; no205+ started. Before any
new op use current branch tables and skip if installed. Sibling dict advances;
latest inspected1f5f2545e..., rw821157fbdd unchanged. Read-only existing source
installations51,120,225,254 can be reused; do not duplicate claimed closure.

Collectors: receipt.py reads launcher logs and direct import object hashes
(post-run, not coherent closure). collect_native.py reads native logs/metrics,
post-run hashes, appends history. Freeze changed per-run sources: exact hashes
must not be attributed to changed current files. Native runs not actual Lean
have #print axioms N/A. Final report under500words with complete table linked,
before/after counts, receipts, git log/base and next deliverable. Use whole budget;
no stop on Kani exhaustion, Aeneas failure, or temporary reservation contention.

Kani5 ASCII8 passes;6 single Unicode scalar passes;7 capacity16 passes. Kani8
push_ascii8 is RUNNING (session43422), after one pre-barrier refusal. No other
capped scope may run until it completes. Check host kani-push-008/output-retry1.log.
New owned.rs mask is recursive (not yet uploaded/extracted); previous loop mask
version is frozen in commit55975ee0c6. New MaskHornerTotal is prepared, not checked.
