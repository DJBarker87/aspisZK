# Native Drop ABI continuation: unaccepted, concrete borrowed-value blocker

Branch codex/cx-prover-rw-20261023; parent c42a29bc58. Design committed first
as 78a5893610. No merge/push, installed tool, shipped crates/programs, protocol,
wire, feature, verifier, security contract, key, or trust change. Candidate
remains unmerged. Both release targets are **not yet established**.

## Exact new progress

The private Extract.extract_Switch repair honors `inside` on Lean switches,
parenthesizing argument-position if/match expressions. Build015 differs from
candidate012 only in src/extract/Extract.ml. On the actual, unchanged V5 Guard
input, extraction042 emits `ok (match drop_glue_back _guard with ...)`.
Whole Guard Lean11574 now has exactly the original swap pair/triple error;
the three `ok match` result-typing errors in11566 disappear. This is focused
printer diagnostic progress, NOT an accepted Guard dependency closure or a
proof of destructor/source behavior. Raw output was never patched. Adaptation
only removes generated source limits and relocates split imports, with hashes.

Candidate013 attempted a generic source pass lowering exact typed nested
core::mem::swap to ordinary LLBC reference/value moves and lifetime ends. It
kept actual precise regular Drop glue and disposal. Extraction037 rejects at
InterpPaths.ml:492, `Could not read a borrow`, at original Rust swap line6.
The ordinary borrow interpreter cannot implement this temporary move route.
The pass is stopped, retained and unaccepted; no interpreter safety check was
weakened. Candidate014 removes that pass and adds a fail-closed guard for
nested/generic swap/take model use; it compiles, but its new nested guard was
not separately exercised (the negative fixtures stop at the existing Main
guard). Candidate015 is an expressly unaccepted printer-only diagnostic;
it retains012's ABI gap and must not replace014 as an accepting tool.

Lean11570 proves only structural permutation equations, untouched abstract
heap/temporary Bottom, and inverse routing for arbitrary callback/carriers.
These are not the missing typed source/loan relation: there is no mechanized
claim about Aeneas contexts, loan ending, Rust callbacks, or actual destructor
execution. No extra tuple slot, trusted ABI, output-equivalence premise,
cleanup axiom or counter1 assumption was introduced. The remaining nested-loan
relation cannot be inferred from these generic equations.

## Metadata correction and extraction boundaries

Pinned Config hash81dd9fdb… sets drop_as_no_op=true. Source-pinned Main maps
-eval-drops to Arg.Clear. New drop_flags.py requires exactly that explicit
switch, exact Config/Main hashes and binding, records every flag and effective
false, and rejects unknown source. All seven new Aeneas invocations use it;
038/040 are Charon plus native reference tests, not Aeneas execution.
Prior baseline020/022 omit -eval-drops; old false labels are unsupported.
Their raw receipts remain unchanged. The static non-no-op branch's omission
of fn_ptr does not show those commands reached that branch.

extraction-inventory.json lists exact retained command arrays and receipt
hashes in this assigned worktree:110 distinct arrays, including scope envelopes
and duplicated logical launches,12 explicit/98 omitted. These are NOT run
counts. Source association is assessed separately: the known pinned default
applies only to associated source. --precise-drops describes Charon LLBC, not
Aeneas cleanup evaluation. No accepted native cleanup/source law follows from
the selected64 commands (030 and new043 reject), or from the noDrop/library
extractions. This inventory is not a claim about all installed backends,
unrecorded commands, or any session A/live worktree.

## Validation and retained failures

All exact commands, effective flags, per-file source/dependency/binary pins,
exit, wall, peak RSS, swap, and full axioms lines are in ledger.json and packet.
Backend013/014/015 pass:6.167/5.172/5.163s,521780/494908/494212KiB, swap0.
Extraction036's ordinary noDrop declaration is byte-identical to032's old
increment. Complete new Types/Funs11571/11572 pass.11573 Guard Types passes;
11574 entire Funs FAILS.11575 is the focused unelided statement/import/axioms
audit of accepted helpers, noDrop and Guard Types; it does not import broken
Guard Funs. Helper equations/Guard/type models have no axioms; noDrop increment
uses only propext, Classical.choice, Quot.sound. Full lines retained. Lean
peaks2629584KiB; all six attempts use the existing5G/7G/noSwap/Tasks64 scope and
global lock (outside the parallel window). No full manifest or unchanged retry.

Independent printer probe Rust v1/v2 passes the same optimized native test
(one test each covering zero, wrapping MAX and None), then Charon038/040 pass.
Both Aeneas039/041 FAIL at InterpExpressions.ml:227, `Can't copy a mutable
borrow`. V2 factors the arithmetic into an ordinary increment helper to avoid
a double-dereference operand; it remains blocked. This is an independent
noDrop probe, not a replacement for original Guard and not backend semantics.
Both Rust sources, raw errors, source hashes and v2 LLBC are retained. The
v1 LLBC bytes were overwritten by040;039's exact input hash survives, as does
Rust v1. This limitation is explicit in source-assessment.json.

Actual selected64 rejects043 and combined native escape/capture rejects044
on014; neither emits Lean. No budget spent on another mutated-input wrapper.
Prior five native Rust tests and original V5 native counter test remain
reference evidence only. No backend recursive/order/conditional/unwind/
loan-writeback source theorem is claimed. No fresh nonzero negative-operation
execution ran: scalar/refined NonZeroI32 implementation files are unchanged
by all candidates (full manifests/diffs retained), with prior validation
reused only at its recorded scope. No scalar coercion was added.

Every new compiler/extractor passed complete-hierarchy admission before launch
and before go; populated reservations remained strictly below55GiB (largest
backend barrier40.375GiB), with exact6G/8G/noSwap/Tasks64. Gate files were
hash/availability-checked before reserving build slots. No OOM or cap increase.
Private cache copying could not read the old root-owned _build/.lock; that
lock was not modified. Scoped compilation reused the remaining copied cache.
Current checks do not repair historical incomplete aggregate evidence.
Post-run tool/source assessments are explicitly labeled; no ELF identity,
performance, installed-tool or adoption gate ran. Source file/binary hashes,
not dirty git labels, identify the experimental inputs.

## Assumptions, stopping point and next producer

Before and after: every existing native/refinement/E1 theorem has identical
statement and hypotheses. None discharged, added, weakened or hidden. No
counter0->1 theorem from actual Guard emission, complete typed borrowed ABI,
source/destructor/E1 closure, or whole-owner claim has been established.
Unwind/postfailure cleanup, unknown/opaque/generic glue, projections and
escaping references remain unsupported boundaries. No Zeroizing/provider,
volatile64/32/fence or simulator work was attempted.

Budgets, all failures charged without reset: backend15/16 (1 remaining),
extraction44/44 (0), Lean236/260 (24), Kani44/60 (16). Stop because actual
borrow-read/copy and ABI blockers are demonstrated and extraction allocation
is exhausted, not because partial emission is accepted. Next producer must
supply a source-backed typed nested-borrow translation/adapter with a complete
input/output/loan-ending relation, then the full original Guard Types/Funs and
counter0->1 kernel regression before recursive/move/conditional/order/writeback
coverage or any Zeroizing/provider work. Additional extraction would require
new allocation; none is requested or assumed by this report.

Literal E1 conditional64 law, OS primitive, actual freshzero64/partial-error
advanced state,16-inner/8-outer loop/ledger/public-nonce policy events and
concrete final tool-boundary review/adoption remain open. Both targets remain
not yet established. The exact source and trust boundaries must be reviewed
at adoption; unadopted candidates inherit no blanket AeneasExtraction trust.
