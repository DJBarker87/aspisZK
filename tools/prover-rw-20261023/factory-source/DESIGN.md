# ProverRwFactorySource fission preflight

UNMERGED / UNADOPTED. Starting revision 4b3e17fb01048bb79c26ff2363a5475827e58f1a.
This design precedes candidate generation, extraction and any production edit.
No merge/push, protocol/wire/feature/security change or new trust is authorized.

## Interfaces and source changes

Before: public generate_for_mask_nonce(nonce32) -> Result<Self, Error> owns
nonce guard, retry=0, while retry<16, fresh zero64, fill?, two zero32 owners,
half copies, short-circuit both-nonzero test, success move or retry+=1.
After: the public signature and nonce guard stay identical. A PRIVATE associated
one_draw(nonce32, retry: usize) -> Result<(usize, Option<Self>), Error> is called
by that actual controller. Its executable body is the verified056 cut exactly;
only visibility/comment/name association may differ. Controller matches helper
result with ?: Some(owner) returns owner; None writes the returned retry and
continues. No helper is made opaque in Rust production. No independent duplicate
cut proof will be pursued. The preflight snapshot is a prospective source edit,
not actual-source progress; successful supported extraction is necessary before
applying the edit to crates/aspis-prover/src/state_only_entropy.rs.

## Ownership and control trace

Nonce zero returns before a draw. Entered r in0..15 allocates freshzero64 and
calls the identical getrandom0.3.4 fill once. Arbitrary partialErr postbuffer is
allowed; identical From wraps the exact Error, bytes64 drops before return,
controller immediately propagates Err. On Ok, construct zero32 field then leaf,
copy the same halves, use the same short-circuit nonzero predicate. On rejection
increment the helper-local retry BEFORE leaf32, field32, bytes64 lexical drops;
return (r+1,None), then controller assigns retry. Thus entry15 rejection exhausts16.
Success moves field32/leaf32 into Self and then Some/tuple/Result, drops bytes64,
returns through controller's match and public Result; public nonce is identical.
Extra return/match moves must be assessed at extraction and native gates. This
makes no promise about stale moved stack copies/registers/caches. Real Drop and
fence stay enabled; no logger/stub/forget/leak/drop_as_no_op.

## Cheap source/extraction preflight and stop criteria

Generate a job-owned selected snapshot from the immutable old factory and056,
with machine-checked spans and exact changes. This is syntactic source evidence,
not old/new semantics. Use at most two extraction slots: Charon precise built
MIR for the prospective controller with just one_draw opaque, followed by the
pinned existing fail-closed candidate014 -eval-drops backend. Its experimental
status is retained; it earns no blanket AeneasExtraction trust. Do not edit any
emitted Lean. Inspect ALL output signatures/externals/Drop declarations before
proposing a leaf interpretation. If extraction rejects glue/ABI or cannot retain
sequencing/Err advancement under existing OS/P6, stop this source path before
production edits. No final backend slot, invariant/full BMC retry or guard/ABI
campaign. A pure function of nonce/retry is not an OS/refinement producer.

056 covers only normal one-draw returned values, custom-u16 errors and retry,
not cleanup events/provenance. It cannot justify an opaque whole-helper event
contract or universal Error. Native-owned-drop leaf evidence is only its exact
source/carrier/frame scope; it does not justify unproved caller events. Before
an actual edit, require a supported leaf boundary matching those facts without
assuming whole-output equality. No premise change is proposed.

## Later gates, only if preflight is credible

After committed source change: focused optimized factory fixed-tape checks
(>=1000; all rejection positions,16-exhaustion,partialErr,zero nonce,order/moves),
local helper timing; all THREE current ELF rebuild/comparison scripts with
current pins, one command per artifact. No old binary identity reused as fresh.
At most3 new focused optimized Rust commands and3 ELF commands, separate from
old unused0/2. Full prover identical-coins>=1000, exact events/native refinement,
E1/L1/L2/L3, outer8 adaptive policy/complete ledger, selected client, quiet median
<15s and H5<=10% remain adoption gates. Generic96 outside scope. Stop affected
fixture slowdown>10%; no hours-long prover gate before design is credible.

Each host attempt independently6G/8G/noSwap/Tasks64; hierarchy before/go
admission strictly<55GiB including visible uncapped service/VM reserve. Preserve
stricter5G/7G Lean if used; no new Lean planned in failed preflight. Pin exact
source/dependencies/binaries/toolchain before and at go; retain command,exit,
wall,RSS,cgroup peaks,swap,revision and full axioms (N/A for extraction).
Budgets at entry: backend15/16, extraction49/52, Lean236/260, Kani57/60.
At most2 Kani this step, reserve last1; none justified by extraction failure.
No frozen manifest. Both deployed targets not yet established.

## Admission correction before extraction

Attempt050 did not launch a scope/compiler/extractor: the added reserve check
incorrectly summed hierarchical uncapped memory.current at every ancestor,
reporting132GB on a62GiB host. Retain its before/preflight data and charge it
conservatively as extraction050. Correct accounting subtracts direct child
current from each uncapped group before summing; finite-covered descendants
remain charged once by MemoryMax. Negative/racing data denies. This corrects
double-counting, not a cap increase or resource-failure replay. The planned
commands move to051 (Charon) and052 (Aeneas), using all remaining extraction
allocation; no fourth command is authorized. Two actual extractions remain
planned, three total preflight slots charged including the failed admission.
