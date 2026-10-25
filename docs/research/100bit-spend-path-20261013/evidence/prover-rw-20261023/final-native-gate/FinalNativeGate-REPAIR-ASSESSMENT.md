# Source-only repair assessment

Base f56c7c533b0fe38b15cc9ddeaab1cef8f9d452a4, assigned branch
codex/cx-prover-rw-20261023. Criteria stage caa9302ede. Exact final source overlay
and dependency hashes are in FinalNativeGate-source-manifest-004.json and the
repair003/audit004 receipts. No merge/push, frozen source/artifact/model/protocol/
security-contract changes, keys, RPC or host access. Public entries disabled;
activation UNAPPLIED. Target source_revision in the plan remains historical;
job_revision distinguishes this wrapper overlay. No new identity gate claimed.

## Established source progress and statement changes

Before: `_tree(roots)` followed every directory symlink and whole-read each file,
with no finite inventory/size/time/cycle bound. `_pins` also whole-read sources;
runtime_pins walked stdlib and whole-read native files. After: `_tree(roots,
catalog)` requires finite reviewed entries, full canonical component/alias
chains and UID/GID/mode metadata, exact early sizes, finite entry/byte/time
bounds, stable no-follow descriptors and entry/FD pre/post checks. Unknowns,
loops, outside-chain aliases, mode/owner drift, short reads/growth deny. Hash
buffer64KiB; reviewed exact sizes bound source/native/runtime hash traffic.
Source/native inventories remain exact at pre/GO/post. Runtime helper semantics
changed explicitly (catalog roles, PATH resolution and bounded maps coverage);
byte-identical callers do not imply unchanged whole-function semantics.
Mutable post-Cargo output discovery has a separate reviewed finite byte/entry/
time envelope; no envelope/cache choice is currently supplied, so it denies.

These are stricter operational preconditions, not new security assumptions or
premise discharge. No theorem statement changed, and no output-equivalence
conclusion is hidden in a premise. Python text/AST and explicit mock tests do
not establish native execution, OS/compiler correctness or complete closure.

Before: outer `_cancel_child` OSError escaped finally before descendants,
guard.finish or terminal writes. After: cancellation, descendant cancellation,
reap, pidfd close, guard.finish/check and receipt attempts retain independent
errors, actual status and null unobserved metrics. The lead counterexample now
reaches cleanup and terminal FAILED under explicit mocks. Inner control-read
failure also retains terminal evidence. Guard finish/reap/cancel/close/check
faults and future orphan-after-wrapper-exit cases are tested. No numeric kill.

Before: a zero wrapper exit plus other checks could yield success. After:
**any spawned child currently produces SCOPE_UNRESOLVED and denies success**.
This is an intentionally incomplete source interface, not a verified shutdown.
The outer actual unit/inode/start/owner binding and bound scope-wide shutdown
are unimplemented. No finite kernel termination promise, no fake empty scope,
no inference from direct timeout-child death. The packet/control path and
UNRESOLVED status are retained. A failed kernel/LSM/D-state reap cannot be
relabeled zero. Do not execute this candidate while that gap remains.

## Cache and setup deliverables

FinalNativeGate-cache-profile.json pins the immutable059 script, actual receipt,
stderr/profile, manifests and MIR records read locally via Git. 059 used
optimized dev opt-level3 and completed its compile phase in the historical
reported0.98s, then timed out124 after243.103s. This is reused evidence, not a
new compile result or timing prediction. MIR used release with dump flags;
ordinary MIR omitted cfg(kani), so it cannot typecheck the reserved harness.
The scalar dev manifest lacks059's profile.dev override. Proposed environment
restores CARGO_PROFILE_DEV_OPT_LEVEL=3; no Rust/manifest edits. Full059 inherited
environment was not recorded; no exact compatibility assertion is possible.

Exact candidate cache locations are059 compact/target and resume-mir/target in
the assessment. No cache is selected, copied, created, uploaded or deleted. MIR
release and059 dev Kani outputs are different; scalar package/path/observer
bytes differ, and original zeroize is added. At least four local package units
need compile/translation work; unchanged libc/cfg-if reuse is only a candidate
pending fresh compiler/cfg/path/profile/fingerprint metadata. Exact time/RSS and
transitive rebuild cost are unknown. No cold dependency rebuild authorized.
Harness, arbitrary quantifiers, sole fill stub, real wipe/observer/control,
solver/unwind66/-j1/240s/3G4G proposal remain unchanged.

FinalNativeGate_setup.py is concrete private no-argument source, with separate
setup adapter/observer/disabled inside entry. Future1G profile,512MiB sampled
resident guard,115s alarm,120s transport,4MiB summary, full strict55/7/2/raw
policy, both scans and once-counted inside cap are explicit. Full numerical
policy source bytes and six immutable bundle inputs are unchanged. Only the
setup adapter fixed unit/high/max/requested cap differ; caller body identity
alone is not a whole-semantics claim. Candidate data publication is exclusive
own0700, bounded and durable; never plan update, sealing, activation or Kani
authority. Derived large remote records would be retained by hash+size in a
public summary, not imported as large Git JSON.

**Setup remains partial/UNREADY**, before metadata allocation: clean setup
environment is null; fresh canonical aliases/Python stdlib/mapped libraries/
child executable/library closure and ownership assessment are unobserved;
cache fingerprints are unobserved; bootstrap source chain and cross-collection
source/native stability join need implementation/review. Deferred records cannot
be silently cleared. Existing raw visibility/control read limits are retained;
the guard/cgroup is not a proof that every raw policy read is bounded. Exact
next source interfaces are listed in FinalNativeGate-SETUP-PROPOSAL.md, including
the fixed owned scope shutdown design. This is the concrete useful ~600-line
repair/setup candidate, not a claim that every requested interface is closed.
Universal compiler/OS semantics is not a prerequisite to resource admission;
finite operational gaps are data, and existing trust boundaries remain.

## Validation and retained failures

New: final repair003 runs22 focused explicit-mock/synthetic-data tests, exit0,
wall0.095717s, peak35,799,040 bytes, swaps0.
Final audit004 exit0, wall0.542012s, peak25,772,032 bytes,
swaps0. Exact commands/source/dependency hashes and full print_axioms=N/A
explanations are in receipts. No Lean theorem/import/compiler invoked. ELF
fixtures parse a synthetic bytearray, not an actual ELF artifact.

Initial17-test log is retained but lacks RSS/swap/exact source-overlay capture;
it is NON_GATE, not a final source identity gate. Repair002 added four catalog/
ELF cases and resource receipts. Its exact full source text is retained in
FinalNativeGate-retained-validation-overlay-003.json, verified against its
manifest hashes. Final repair003 adds source inventory coverage checking:
_file_pins now traverses the exact source catalog roots and requires snapshot
coverage equal to all sealed source pins, rejecting unknown directory entries
and unpinned source files. This source change justified the new focused check
and regenerated source seal/audit. No unchanged full-policy regression ran.

Reused: lead28 historical mock passes, six immutable bundle byte identities,
059 and MIR provenance. Lead original mistaken Mock-path failure and corrected
counterexample/review are copied unchanged. No old fixture receipt is rewritten.
Base f56 is immutable Git; before/after complete source diff and function hashes
are retained in source-diff004/function-identity004. Runtime/guard changes are
explicit. No target was closed from mocks, and no claim of accepted execution.

All actual host/SSH/network/metadata/setup/native/compiler/Rust/Cargo/Kani/Lean/
extraction/backend/ELF/root/sudo/namespace invocations: ZERO. Python mocks/text
only. Final Kani59/60 reserved; Lean240/260, Rust2/3 (ordinary actual1),
extraction54/56, backend15/16, ELF0/3 unchanged. Both security targets NOT
ESTABLISHED; all native-world/refinement/controller/finite16/outer8/E1/full
transcript/L1/L2/L3/client/adoption/artifact/performance obligations remain.
Stop for source review. No SSH or final Kani allocation requested or consumed.
