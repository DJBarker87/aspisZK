# Port22ARENA selected primitive, pre-execution design

Base: 51ff811857e6f2928b03b5647c3b247a36335928, branch codex/cx-port22arena-20261024.
Only new proof/tool/evidence files; no production changes, trust installation,
ELF rebuild, backend change, full manifest or other-owner mutation.

## Pinned body and exact target statements

Source: solana-program-entrypoint 2.3.0 src/lib.rs lines 341–364,
SHA256 027efed4018bc8f1a340e576bbb0135cb70ba31fc465a23f4732ff8d5196d919.
Actual cost-probe selects start=HEAP_START_ADDRESS, len=256*1024,
target_os=solana, not the host extraction's Global allocator.
Reuse Port21 runtime-source-graph.json and std-source-graph-complete.json
as historical exact-source evidence; independently verify relevant hashes.

Define initial(s,l,c) := if c=0 then s+l else c.
Define candidate(s,l,c,n,a) := (initial(s,l,c)-n) &&& (2^64-a).
Nat subtraction represents usize::saturating_sub. For legal power-of-two
a=4 or a=8, 2^64-a is exactly the 64-bit complement of wrapping_sub(a,1).
No claim for invalid Layout or overflowing arena addition.

Planned kernel statements (universally quantified natural addresses):
* candidate <= initial-n; candidate mod 4=0 at a=4, mod 8=0 at a=8.
* If c=0 or c<=s+l, and s+8<=candidate, then
  s+8<=candidate and candidate+n<=initial<=s+l.
  Thus the allocated byte interval excludes the cursor word and old upper
  allocations. Saturation cannot turn insufficient space into success.
* Interpret the literal cursor store as eight little-endian byte writes at
  [s,s+8). Null branch performs no write. For every address x outside this
  interval, resulting byte equals its input byte on BOTH normal branches.
* Source-order primitive trace is read-cursor; on success write-cursor;
  return pointer/null. Every abort cut retains the caller's prior ordered
  history and exactly the executed prefix. This trace is an explicit
  mathematical body interpretation, not an asserted native execution fact.

## Vec/control bridge and smallest remaining native interpretation

Vec::new gives len=0; Vec::try_reserve_exact passes self.len BY VALUE and
borrows only self.buf. RawVec grow_exact checks addition/layout, allocates,
and set_ptr_and_cap writes ptr and cap only. For a fresh non-ZST Vec,
current_memory=None, so no realloc/copy/free old allocation path is needed.
The native obligation is NOT a whole-helper record:

Before (Port21 external): reserve T : Vec T -> usize ->
Result ((core.Result Unit TryReserveError) * Vec T), with arbitrary post Vec.
After (required, NOT assumed): selected fresh RawVec path, under admitted
nonalias arena/header layout, has actual Ok or Err result, and writes only
RawVec ptr/cap fields plus allocator cursor bytes. On normal return the
unborrowed len field therefore remains zero; initialized range [0,len) is
empty. Abort yields only the reached prefix, no returned Vec/normal cleanup.

Native interpretation needed: valid aligned cursor load/store with eight-byte
footprint, integer/pointer cast provenance, disjoint exclusive buf reborrow,
allocator shim selection/null conversion, and runtime abort prefix semantics.
The body arithmetic/frame theorem proves the cursor-store part of this route;
it does not invent those ABI semantics. A source-matched mathematical theorem
alone is not a native theorem. Field disjointness must come from actual layout
and runtime admission, not absence of a Digest parameter.

Once that primitive is connected: actual map_err maps reserve Err to Allocation
and skips resize. On Ok, len=0 and capacity>=n; resize takes extend_with for n>0,
its reserve cannot grow, writes n-1 exact full clones then moves the final
value and SetLenOnDrop sets len=n. n=0 takes truncate(0). QM31 clone is emitted
identity on FOUR u32 fields; [u64;4] selects Copy array specialization, retaining
FOUR full u64 fields. No scalar-only proxy or arbitrary reservation Bool.
This content route is conditional until pointer writes/len guard are interpreted;
no whole-helper equality, noHash assumption or privacy cleanup claim is added.

## Literal existing policy assessment

D157 LOG lines8389ff permits pure std methods but explicitly excludes allocation
failure and unsafe. D189 LOG lines9001ff supplies native AccountInfo/heap SDK
interpretation and snapshot allocation under existing private runtime allocator
premise; S2W design1210ff makes that account projection explicit. It is not a
Vec initialized-content or oracle-effect law. P2 in R1-PREMISES-REACCEPTANCE
supplies ownership, permission, locks, rollback, persistence; P7 preserves
reviewed source semantics in the exact selected ELF. Neither proves a missing
Rust unsafe primitive interpretation; P6 does not certify handwritten semantics.
S2H design163ff retains observed abort histories despite rollback. No new trust.
Port21 probability projection is retained: physical whole-heap equality is not
automatically required. All-outcome ordered query accounting remains separate.

## Validation and budget

Commit this design before proof execution. Small primitive module first, then
source-control dependent bridge, then one full statements/axioms import audit.
Warm local Lean -j1 -M4400 -DElab.async=false, job-owned objects, global atomic
lock and aggregate8GiB stop. No cold builds. At most13 Lean attempts,1 Kani,
2 extraction; no unsupported-shape extraction repetition. Initial global charge
320/368; job allocation13; unassigned35. No Kani/extraction/Rust required for
arithmetic proofs. Preserve failures. Exact commands, source/dependency/tool
hashes, exits, wall/RSS/swap and full axioms in receipts. Native producer remains
open unless actual ABI linkage is established; both security targets remain open.

## Native focused check, statement frozen before execution

One Kani invocation: Port22ARENA_selected_alloc_frame. Exact SDK struct/new/
GlobalAlloc source copied byte-for-byte, supplied imports only. A 256-byte arena
is embedded in 34 native usize words, guard words outside it. Arbitrary initial
bytes, cursor zero OR start+offset (8<=offset<=256), arbitrary nonzero valid Layout size,
alignment4 OR8; arbitrary observed word index except cursor. Assert actual
unsafe alloc preserves that word, actual returned pointer/null and actual cursor
match the source arithmetic, successful range/alignment. Invalid Layout returns
before the call; null allocation is not excluded. This is a native Kani-model
finite-arena check, not the deployed fixed-address 256KiB arena, no Vec/std
extraction claim, no native oracle-trace or abort-handler theorem. Its actual
integer/pointer support is tested, never replaced with assumed pointer laws.

Native preflight correction: size=0 is outside GlobalAlloc::alloc safety contract; fresh Vec additional=0 skips allocation. Harness returns before that call, rather than interpreting UB. This is a reached primitive precondition, not successful-allocation conditioning.

## Dependent field-frame statements, before Lean execution

Define readLE mem base count recursively for little-endian bytes. Define
Separated u v := u+8<=v OR v+8<=u, without inventing Rust field offsets.
Prove: eight-byte cursor/ptr/cap stores at pairwise length-disjoint addresses
preserve readLE of the length word, on any prefix of these stores. Specialize
to actual source write order: allocator cursor, RawVec ptr, RawVec cap;
capacity-overflow/null prefixes and normal Err contain fewer stores. A fresh
length read of zero remains zero, so its initialized index range is empty.
This derives the byte-frame implication from explicit disjointness, rather
than assuming the post-length. Native association still must identify actual
field addresses, writes, and admitted private arena. The passing finite arena
Kani check supplies its selected allocator side only, not those Vec addresses.

ReadLE/store representation is a mathematical memory interpretation, not an
edit to Aeneas Vec, installation of a primitive record, or general noRO law.
No whole-helper conclusion appears in a premise. Error mapping is the literal
pinned Result::map_err match; a reserve error remains Allocation independently
of resize. Full Clone source association is recorded separately; no new
content wrapper will be presented as concrete native Vec progress.

## Word-body bridge, statement before execution

Add a separate source-word module: define the literal 64-bit initial cursor
(if zero then wrapping start+len else cursor), saturating subtraction by branch,
and bitwise AND with complement of wrapping align-1. Prove its toNat equals
candidate start len cursor size align when all operands fit 64 bits, start+len
fits, and 0<align. Prove the wrapping-complement equation independently first.
This discharges the integer representation link; pointer casts/load/store and
Vec shim remain different native obligations.

Source detail correction: pinned host array specialization is on TrivialClone,
not merely Copy. core::clone impl_clone explicitly includes u64 and gives both
clone=*self and unsafe TrivialClone; specialized array clone uses ptr::read of
the FULL [u64;4]. This still needs the selected native read interpretation.

## Focused final audit

Import Port22ARENA_VecFrame and Port22ARENA_WordBody; print all definitions,
check all21 complete theorem signatures, and print axioms individually. No
new theorem, native assumption or release composition. Runner now records
complete transitive core/job module/source/olean/sidecar/tool-library hashes,
verifies them under the shared lock at go, and uses only job objects plus the
Lean sysroot in LEAN_PATH. Earlier focused receipts retain their original
direct-dependency at-go hashes; later closure assessment is not retroactively
attributed as an earlier fresh gate.
