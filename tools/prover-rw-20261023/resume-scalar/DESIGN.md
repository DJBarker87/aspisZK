# ProverRwResumeScalar design

Entry 7e900bb53455a1758fe24014d1987f08d6cbb242. Prospective job copies only.
Commit design before source. ZERO Kani, including compile-only. No extraction,
backend, ELF, production, key, chain, service, other owner or candidate changes.
Keep 058/059 packages and timeout receipts untouched; no retry or raised timeout.

## Exact target, before and after

Before: ResumeP6's unrestricted nonce32, initialized postbuffer64, entry0..15,
Ok or Err of every valid host NonZeroI32; real Request::draw and Draw::resume,
real Zeroizing Drop, array iterator, scalar volatile writes and fence. Three
full before/after snapshots attempted bytewise result/frame/cleanup assertions.
After: the SAME source contract and quantifiers, with ONE j in0..31 chosen at
harness entry. Observe only j for32, j and j+32 for64, using live typed borrows
inside Drop. Fixed {len, low:u8, high:u8} observations; no array observation
loops, full snapshots, child pointer retention, owner layout metadata or dead
object reads. Arbitrary complete input arrays and the original zero tests,
copies and wipes remain. Universal j proves each32 coordinate and both64 halves;
it does not restrict inputs to sparse arrays or independence assumptions.

## Total ghost design and roles

Metadata is disjoint static storage in the job copy. Coordinate set once before
any source call; no source reads ghost state. Use bounded slot selection and
three separate scalar events, with no array indexing or unguarded count
increment. Unsupported types yield a sentinel observation, not panic. A full
log sets overflow and never wraps. The actual selected normal paths must rule
out sentinel/overflow; no assumption that an event ordinal identifies an owner.
Bind roles to concrete source local moves, return aggregate fields and drop
sites. Success64 cleanup precedes return; moved32 owners remain LIVE until the
harness's later disposal. Rejection increments retry before reverse lexical
leaf/field/64 cleanup. Err constructs no32 owner. Equal payloads have no role
identification function.

## Relation and validation

Prepare identical original/instrumented selected source modules with distinct
zeroize package identities, and a same-input paired harness. Compare actual
control, error, nonce, selected returned coordinates, and ghost frame after the
original execution. Boundary provider ledger is bookkeeping, never OS World.
No assumed whole-output equivalence structure. Give an explicit store projection
and source-step argument for inserted typed reads/static writes; document the
exact remaining compiler/native provenance and unwind boundaries. A syntactic
reverse patch and a finite Lean model alone cannot close native erasure.

At most one optimized host Rust compile/check may produce the concrete MIR role
binding; no runtime test gate. Use a fresh job directory, pinned packages/tools,
before/go full-hierarchy reservation gates with resident+7GiB reserve and strict
<55GiB, scope High6G/Max8G/Swap0/Tasks64. No launch after denial. At most8 focused
Lean compiles (starting236/260), warm pinned local -j1 -M4400 under atomic lock
and aggregate8GiB guard, no cold/full replay. Compile smallest lemma, dependent
bridge, focused axioms/import audit only when useful. One final packet audit.

Expected graph reduction:059 stored3*2*64=384 payload bytes and copied that log
at every event inspection. New log stores3*2*2=12 payload bytes (32x reduction),
no per-element observation loops. Two selected source executions in the paired
harness still retain real source copies/scans/wipes; no solver-time claim.

## Retained obligations

No new trust assumptions or premise discharge by renaming. Literal contextual
successful64 E1 remains unchanged. Native operational state is not OS World;
error/world transport, actual reachability/rank, finite16, outer8 adaptive
policy/durable ledger/full transcript, L1/L2/L3, selected client, native refinement,
all3 current ELF, fullprover1000 identical bytes and quietmedian<15s/<=10% slowdown
remain. Both deployed targets not yet established. Kani59/60 last slot reserved;
extraction54/56, backend15/16, Rust0/3 and ELF0/3 carried. Record source, package,
tool/sysroot/dependency pins and exact command/exit/wall/RSS/swap/full axioms.
