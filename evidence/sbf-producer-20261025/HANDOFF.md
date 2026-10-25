# SbfProducer handoff

Branch codex/cx-sbf-producer-20261025; entry
338af425c97277de9bb3c9bd7d6f7c4841cc6f53. SOURCE/DESIGN/CRITERIA committed
191f06822f before implementation. All work is confined to the two assigned
paths. No merge/push. No shipped crates/programs/protocol/security source edit.

## Established source claim

`SbfProducer_continue.py` contains a concrete parameterless user producer and
root-helper continuation for the fixed 3G/4G/Swap0/Tasks64 user unit. Both call
the actual copied full read-only collector/evaluator, not a projection, marker
or caller-supplied truth. Own Q0 accounts for the finite 4GiB cap once; the
55/7/2GiB policy and full raw scans/visibility/error behavior are unchanged.
Package, fixed launcher, root task sudoers policy, interpreter/runtime,
environment, inherited limits, process identities, controls and actual bounded
sudo/optional-monitor/helper ancestry are checked. Unexpected inherited FDs
deny; fixed readonly null0 and write-only null1/2 are explicit before sudo.

The candidate reaches the concrete `producer_fixed_body -> internal_backend`
call only through its full source control gate. Guest setup still uses the
reviewed concrete capture/new mount root/drop/stdio/zero-exit public-output
implementation. The finite lifecycle delta adds owned parent pidfds,
PDEATHSIG arming/rearming and liveness checks across credential drop, plus root
termination through existing owned-child cleanup. Unchanged modules reverse to
exact reviewed bytes; unchanged extracted/backend functions pass AST equality.
Full before/after backend source is in SbfProducer_backend_delta.patch.txt.
965 new implementation lines, including tests/receipt runner and excluding
exact copies/duplicate patch representations: see source-audit accounting.

No equivalence/security/native theorem or formal premise change is claimed.
Before: reviewed CLI always denies, producer/runtime null. After: public CLI
still always denies; separately reviewable internal integration now exists,
with no report, command, runtime-path or code argument to either entry.
No no-op/generic callback is substituted for concrete collector/backend work.

## New versus reused validation

Exact argv/source/interpreter/dependency hashes, exit, wall, peak RSS and swap
are in the following receipts; axioms are N/A (no Lean/theorem invocation):

* SbfProducer-focused-receipt.json: 13 tests, exit0, 0.101166833s,
  40124416B peak, swap0, source16d146fe6389f0d8eae7eea53c37ca4aaaada1b9.
* SbfProducer-fd-focused-receipt.json: three changed FD/root-order checks,
  exit0, 0.064133791s, 36356096B, swap0,
  source7bbdeb767e5c5ddd857d4971269494580f3bd1e8.
* SbfProducer-package-focused-receipt.json: three affected package/FD checks,
  exit0, 0.053551292s, 34488320B, swap0,
  sourcedc01907f5ec7188ff19c0ae18d2be43cba4bdfdb.

After each meaningful source change only affected checks were run, not an
unchanged broad regression. Pure synthetic raw snapshots recompute actual
policy; explicit mocks replace individual live read/process/native APIs.
Tests cover deductions/count-once, projection/old1G/wrong-unit and controls,
source/env/maps/limits pinning, ancestry routes/start drift, package writers and
links, initial FDs/access modes, guest gate/owned-pidfd failures and collection
ordering. None executed real collection, subprocesses, ctypes CDLL, fork,
signals, scopes, privilege changes, native backend or host operations.

Both failed test approaches/logs/receipts remain: first two fixture/platform
errors, then a misplaced mock assertion. The first receipt's mistyped revision
argument is explicitly corrected in its assessment, never silently rewritten.
No resource failure was rerun. SbfLinux's 54 unchanged cases are historical
REUSED evidence, not rerun. All six resource failures remain immutable and are
hash-referenced in SbfProducer-historical-assessment.json; the 552960B denial
remains a denial. No Meta1G GO is used as authority. No old report replay ran.

## Ready artifacts, unready execution

Ready for lead source review: design, full source, identity map, static
import/source audit, raw successful/failed mock evidence, exact 17-file
root-owned installation hash/mode/path inventory, fixed launcher, narrow
zero-argument NOPASSWD/NOSETENV sudoers line, cleanup semantics, backend delta
and separate UNAPPLIED activation patch. Root installation must freshly copy
into root-owned exclusive inodes, never promote user staging with live writers.

UNREADY: published complete runtime manifest/hash/signatures are absent.
Runtime087 is not approved; RuntimeTrace58497 files/logs were not read.
No tuple/null metadata or CLI flag activates installed entries. The activation
patch alone cannot make execution pass; a future reviewed release must supply
the trace closure and regenerate all package/external installation hashes.
Root/interpreter/loader bootstrap trust remains an external installation gate.
All full runtime/project/kernel/native/security assumptions remain; none is
discharged or newly assumed by mocks. LSM SIG0 versus SIGKILL, monitor orphan
routes, PDEATHSIG/exec behavior, D-state waits and bounded reaping remain OPEN.
Sampling/freshness never guarantees future physical memory headroom.

Every actual host/SSH/network/root/sudo/ns/mount/fork-exec/security/rlimit/
scope/admission/probe/compiler/Lean/Kani/Rust/Cargo/extraction/backend/ELF/key/RPC
budget used: ZERO. Keys untouched. Existing ELF pins unchanged. No final
manifest replay or frozen-source change. Both deployed security targets remain
not established. Next deliverable: lead review of this source delta, then the
future published runtime-trace closure and separately allocated deployment/
probe review. No approval request to Dominic at this stage.
