# Original claim inside native preparation, 2026-10-25

Target not yet established. The accepted partition list and remaining work are
in packet metrics.json, not inferred from the presence of harness declarations.
At initial sealing, point0 (any first-row push failure) and point6 (all174 pushes
succeed) are checked. Points1–5 remain pending. No whole claim/cone closure.

## Actual source connection checked

Predecessor 1bd903c2d2 checked original Prepared::new with complete frozen
transcript and powers::<29> bodies, but substituted prepared_claim itself.
The new native harness removes that cut and runs the COMPLETE original
prepared_claim body in the SAME constructor call. No opaque claim replacement,
reference-only constructor, transmute or simplified Verified/Prepared carrier.

Both gamma powers29 and kappa powers7 execute the adopted early-return helper.
Under primitive multiplication returns, success checks 28+6+7=41 ordered
multiplications:28 gamma,6 kappa,7 final weighted products. The claim source
constructs each native EbyKDot, pushes the same caller scratch entry and exact
semantic scalar in column order, consumes each returned dot, and accumulates
seven products in the original add order. The actual returned claim equals
the final sum leaf return, and the complete Prepared fields/state are checked.

Each push checks all eight u64 accumulator words and usize count before and
after the preceding mutation. At each new point all these fields are zero,
derived from actual EbyKDot::new. Push-result tapes cover arbitrary typed native
states, with no raw/private-carrier transmute. Scalar provenance is the actual
native sem.claims[point][column], extra[column], before_z1[column], or c0 of
the field parser's return at the SAME y1 pointer and column. Finish checks
that same last state and exactly29 preceding pushes. No desired dot arithmetic
equation is assumed or proved by this control result.

Query rejection retains all30 actual digest reads and performs no claim work.
Query success retains33 reads before gamma/claim arithmetic. Every claim push
error maps to the source's Parse, stops at the checked first failing call,
preserves completed gamma scratch, and skips the final aggregation. Complete
success checks174 pushes,6 finishes,29 field calls,7 final adds. The existing
transcript preimage/order checks and complete native release carriers remain.

## Boundaries, source and private access

Nine normal-return cuts: gamma/ordinary/QM31 sampling, queries_from_pairs,
WideExact mul/add, EbyKDot push/finish, weights.field. Scripted Digest32 checks
actual preimages but permits inconsistent replies to repeated preimages, so
this is not concrete hash/oracle probability transport. Dot/field/arithmetic
semantics and initialization/allocator/SDK/runtime/SBF joins remain open.
These new cuts replace the HIGHER prepared_claim cut; they do not discharge
the primitive implementations or install the Kani result into a Lean theorem.

Complete selected source bodies/carriers remain pinned to freeze
25866ec331cc7ce27dd9956609c11d32fa8fa58a. Only proof accessors were inserted in
the source-only harness copy of fast_pairing: canonical::Dot exposes its four
sums, EbyKDot exposes all eight sums/count, plus corresponding typed constructors.
The checker removes exactly those cfg(kani) additions and verifies the complete
original frozen fast_pairing source byte identity. Arithmetic bodies/fields are
unchanged. Production and S5 tracks were not modified. No source adoption,
release artifact re-pin or protocol/security decision is claimed. The factored
native context and SDK association still need the standing integration gates.

S2 framing/canonical private E domains and default allocation-success/no-uninit
checking are retained. Arbitrary typed QM31 semantic inputs remain covered under
the normal-return cuts. This is not arbitrary-input TOTAL or a proof of the
actual native decoder/allocator. Existing Lean parsing, powers, borrowed-claim
meaning and same-caller ranges/trace results are reused, not recompiled.

## Focused validation and retained failure

Kani0.67.0, rustc1.93.0-nightly53732d5e0, warm two-package arm64 workspace;
exact optimized flags/tools/source/import/command hashes and immutable snapshots
in each input/receipt. Native snapshot source revision428aa8f7e5 plus explicit
source hashes. Source-only reconstruction matches every input hash. No compiled
objects/GOTO programs are published. #print axioms: N/A, Kani only; no new Lean
axiom or theorem.

- v1 smallest changed target compiles exit0,1.125832166s,RSS524140544B,swap0.
- v2 broad-unwind first-error target was terminated by the180s wall watchdog,
  exit-15,180.102223s, sampled aggregate4671209472B; final peak RSS and swaps
  unavailable because time(1) was terminated. No proof credit, no OOM claim.
- Read-only --show-loops identified original claim inner/outer/aggregation
  loops. v3 uses bounds30/min(point+2,7)/8 WITH unwinding assertions. No
  assumptions disable incomplete paths. Source/body/input domain unchanged.
- v3 point0 passed0/3007 checks,169.916609s,RSS4906680320B, sampled aggregate
  5369069568B,swap0;2/3 covers (query error/claim error; success unreachable).
- v4 success target compiles exit0,1.117686s,RSS521928704B,swap0.
- v5 success target passed0/3006 checks,212.738691s,RSS5074632704B, sampled
  aggregate5711560704B,swap0;2/3 covers (query error/success; claim error
  unreachable). The solver and external wall allowance are600s for subsequent
  distinct partitions, based on measured v3 timing; same6GiB memory guard.

One local atomic compiler lock, one job,6GiB aggregate sampled RSS guard,
explicit process limit64. No cold dependencies, NUC/SBF build, package replay
or unchanged accepted-target replay. remaining.py compiles each remaining
changed harness first, verifies it, checks its authoritative receipt and stops
on any failure. It never runs partitions concurrently. A checker string-match
initially omitted unsafe global access syntax; corrected without compiler replay.

The other five claim-error partitions must pass before crediting coverage of
all174 possible failing push positions. Even all seven normal-return partitions
would leave concrete leaf/runtime/extraction/caller/release obligations; this
packet does not close S1/S6 or the100-bit source security target.

## Addendum: completed rows and retained resource failures

The sealed metrics now accept points0/1/2/3 and6. In addition to the initial
success and first-row error results:

- v7 point1: exit0,155.663742s,RSS5638406144B,aggregate5887410176B,swap0.
- v9 point2: exit0,211.970360s,RSS5848367104B,aggregate5775212544B,swap0.
- v11 point3 (extra): exit0,215.317782s,RSS6359351296B,
  aggregate6260031488B,swap0.

All use the exact initial proofs.rs, same native bodies/carriers and normal
cuts. Their smallest changed harnesses compiled first (v6/v8/v10). Source-only
receipts/commands/tool/source/import pins and read-only checks are included.
Points4/5 remain OPEN; no passing declarations or failed attempts are credited.

Retained local failures: v13 original point4 hit the6GiB sampled RSS watchdog
at305.945357s/6455508992B aggregate. v14/v15 changed expected scalar reads to
exact typed copies of the SAME semantic inputs; compile passed, verify still
hit6GiB at276.481585s/6461177856B. v16/v17 shortened ONLY the unused test-output
tape to145 reachable push returns (point4 failure positions116–144), preserving
all source inputs/fields/cuts; compile passed, verify hit its initial7GiB cap
at117.734342s/7601029120B. The latter was a materially reshaped target, not an
unchanged bigger-cap replay. For these terminated process groups time(1) never
reported final peak RSS/swaps: those metrics are UNKNOWN, not zero.

The two failing-row ranges were then split into0–14 and15–28, whose union
covers all29 columns, with full174-entry native state tapes restored and
expected semantic copies. This is proofs-halves.rs, a candidate only. The NUC
first refused12GiB before scope/compiler creation: its old admission added
whole-host occupied counters to full capped reservations that already cover
some of those residents. A separate new runner retains every populated finite
MemoryMax reservation, requires their sum plus the new cap below the host's
safe limit, and requires MemAvailable above ALL those full caps plus9GiB.
Whole-host counters are retained as context, not added twice. This is an
operational snapshot/headroom policy, not a formal bound on future uncapped
growth; no resource limit of another owner was changed.

NUC v2 used10GiB high/12GiB max/Swap0 and fresh admission. The focused Linux
compile passed4.874946s. Reading the unnormalized .symtab.out yielded no loop
IDs, so validation stopped BEFORE verification. v3 reuses that exact closed
owned source/cache and compile receipt/tools, reads normalized .out identities,
and enables all unwinding assertions with source bounds30/6/8. Its first lo4
half timed out after500s (exit1,504.453952s,maximum RSS10981212KiB,
CG peak11267641344B,swaps0,no OOM). MemoryHigh logged60329 events. v4 changes
ONLY the resource environment to12GiB high/14GiB max with new admission and
an exact compile reuse. It also timed out (exit1,504.422522s,RSS12973008KiB,
CG peak13311078400B,swaps0,no OOM),106751 high events. Neither is a theorem
failure/counterexample or a passing proof. High pressure may contribute to
wall time, but the records do not prove it is the only cause. No other half
was launched. Raw terminal source/text histories and immutable runner/plan
versions are retained in nuc-history-v1/v2; transport source archives contain
no binaries. The source/cut domain and14GiB attempt remain explicitly candidate.

Full-constructor retries were stopped after these diagnostics. The next proof
shape checks the canonical TEST-input generator once and uses verified contract
stubbing, rather than repeatedly validating it throughout the whole controller.
The generator is not a protocol sampler or a new source assumption. Its
private native E return requires a verification-only raw Arbitrary extension
followed by the checked canonical postcondition, isolated in a separate candidate
core workspace; the native fields and existing functions remain unchanged.
This candidate has its own source/tool/import pins and must not be attributed
to these historical original-core proofs. No raw return is used for arithmetic
before the canonical postcondition. No production edit/adoption is requested.
All remaining primitive/SDK/runtime/extraction/oracle/release obligations stay
open regardless of whether that optimization eventually passes the late cases.

## Later-build pin correction

These receipts retain historical component25866 pins. The current release
ledger identifies later build source4bb3b3f51e; see
[S126-FREEZE-RECONCILIATION-20261025.md](S126-FREEZE-RECONCILIATION-20261025.md)
for exact unchanged selected items and changed lower/core/adapter contexts.
No whole-release/source transport is inferred from these historical checks.


## 2026-10-25: first late-error half passes with increased memory

The user authorized more memory. NUC v6 changes only the resource/admission
configuration of the exact v2 compiled source/tool kit: MemoryHigh23GiB,
MemoryMax24GiB, MemorySwapMax0, one solver. Fresh admission counts all populated
finite caps against the safe host cap and requires MemAvailable to cover their
unused headroom plus4GiB additional reserve. Already resident capped memory is
already excluded from MemAvailable. No other owner's limits changed. v5 retained
the earlier9GiB extra-reserve rule and refused admission before launching.

`verifier::proofs::prepared_new_claim_lo_point_4` PASSED: exit0,
347.940938063s, peak process RSS12973036KiB, cgroup peak14375067648B,
swaps0, zero high/max/OOM events, 0/3027failed and2/3covers. Exact sources and
tools were unchanged; the focused compile was reused with pinned receipts.
This checks the native constructor/transcript/powers/original claim through
before_z1 push errors at columns0–14, plus the existing query-rejection branch,
under the SAME nine normal-return primitive cuts. It does not discharge those
cuts, allocation/initialization/runtime/extraction/oracle or release binding.
No new hypothesis or frozen source change was introduced.

Before: both halves of point4 and both halves of point5 were unverified.
After: point4 columns0–14 are checked; columns15–28 and both point5 halves
remain unverified at this snapshot. Full point4 is not yet closed. Earlier
points0/1/2/3 and complete-success6 remain checked as previously recorded.
The old14GiB run timed out with106751 high events; the successful24GiB run has
none. This supports increasing the throttle threshold; it does not establish
that memory pressure was the only cause of the earlier timeout.

Source-only packet: `evidence/s126-current-caller-20261021/`
`s1-native-prepared-claim-memory24-terminal-v1`, read-only checker
`tools/s1-native-prepared-memory24-20261025/check.py` PASS21pins. The packet also
contains an explicitly nonterminal hi4 launch snapshot; only lo4 is accepted.
Kani has no Lean #print axioms result (N/A), and adds no Lean axiom. Native
historical25866 context remains distinct from current whole4bb3 source, as
specified by the freeze reconciliation above. S1/S6 and the security target
remain OPEN. The next running target is the complementary hi4 partition.
