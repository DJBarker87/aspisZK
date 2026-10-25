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
