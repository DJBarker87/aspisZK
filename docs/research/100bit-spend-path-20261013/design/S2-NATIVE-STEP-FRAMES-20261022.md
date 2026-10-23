# S2 native cleanup and concrete account regions

S2/S1/S6 remain open. This packet closes focused cleanup and address-binding
checks, not the enclosing actual-source caller obligation. No production
source changes, protocol change or source adoption is requested.

Source-only packet: `evidence/s126-current-caller-20261021/sdk-native-step-frames/`.
Reproduce its source/receipt audit with
`python3 tools/s126-sdk-modular-20261021/check-native-step-frames-packet.py`.
The packet identifies exact tools, generated sources and dependency files;
source revision in host receipts is host bookkeeping, not attribution of that
revision to the adopted release. The authoritative adoption is still
25866ec331cc7ce27dd9956609c11d32fa8fa58a, S4 adoption
29cbab431742f7e899870595167efa193a379f0a. Research inspected at
1c6059dd31a6c246844ce8bb2380532e8a4225b9; C3-BIN latest addendum12:40 retains
default40dc7574/devnet12cb0bc2/Pool121f3e29. Transitive source re-pin remains.

## What passed

The direct `ordered_cleanup` contract executes actual typed SDK Ref/RefMut,
full statement Box and checkpoint Vec destructor bodies. Its only deallocation
stub dispatches to the actual frozen SDK BumpAllocator dealloc body. It permits
writes only to the three actual data borrow counters and proves their exact
restoration. No SDK/guard/Drop model or verified callee stub is used.
The actual account data uses arbitrary full-sized stack-backed slices; this
is a concrete valid-memory class, not arbitrary runtime-layout completeness.

A separate ordinary harness proves the actual SDK guard data pointers/lengths
and all counter/data separation inequalities, plus disjointness from the
actual account containers, descriptors, Rc headers, lamports cells, amounts,
keys and owners. Its five cleanup helper bodies exactly match the first check.

The saved GOTO fragment of the successful original native paired caller shows
copy followed by checkpoint Vec, proof Ref, statement Box, public Ref and
checkpoint RefMut destruction, then success; all seven jumps are unconditional.
This certifies the compiled order/control fragment, not an independent Rust
move/relocation semantics or runtime equivalence theorem. The inspection pins
its prepared program hash; the older paired packet pins raw GOTO and commands
but has no independent ready.out hash, so that extra hash join is not claimed.

Lean `S2NativeStepFootprintsV1` and `S2NativeTailAccountViewsV1` prove frame
composition and exact byte-view consequences for data sizes58295/1880/1768
and8-byte counters. Their concrete source-step premises remain external;
no new opaque native function, custom axiom or presumed enclosing frame is added.
Before: separate copy and cleanup effects. After: their conjunction plus checked
separation implies unchanged proof/public/protected views and saved1768-byte
checkpoint. No enclosing native accepted-run premise has yet been discharged.

| Target | Exit | Checks | Covers | Wall s | RSS KiB | Swap |
|---|---:|---:|---:|---:|---:|---:|
|sdk-ordered-cleanup-direct-frame-check-v1|0|1865|2/2|116.06|6426180|0|
|sdk-cleanup-region-bindings-check-v2|0|1964|2/2|36.599|1955424|0|

Both optimized, one job, fresh admission, MemoryHigh6G/MemoryMax8G/SwapMax0.
Kani axioms: N/A. Exact inventories and receipts retained. Local Lean targets:
footprints-v2 exit0,5.128523041s,667254784bytes,swap0;
tail-account-views-v1 exit0,4.570309541s,668385280bytes,swap0.
Nine `#print axioms` reports contain only standard Lean axioms (some empty).
Exact imports: `native-step-frames-import-pins.json`; atomic local lock,
-j1 -M4400. No unchanged full replay.

## Excluded attempts and remaining work

Nested-contract cleanup checks timed out (204.721s/6540124KiB and
204.457s/6553208KiB). Removing nested verified stubs gave the direct green
check; changing payload storage alone had not fixed it. Initial region probe
failed borrow checking and was corrected by capturing the original amounts
pointer before borrowing. A full reference snapshot built before native
execution timed out at187.82s/6527816KiB; successful codegen is not proof.
All remain excluded. The first local footprint attempt had a reserved-name
compiler error and receives no proof credit.

Next is fixed-initial caller composition using existing native first-entry
facts, exact gate/scanner normalization, successful reference constructor and
these tail effects. General valid heap/SDK ABI/allocator interpretation and
source cleanup relocation remain explicit, as do concrete installed pure
children and ordered oracle effects. The lead's14-field interface also needs
writer/account/TX2-reader checkpoint transport and fixed public retention or
reconstruction. Cross-TX hash equality is not byte equality; no collision term
or query budget is silently added. S6 and S1 composition remain behind that
caller connection. Target not yet established.

## Actual implicit cleanup follow-up

`evidence/s126-current-caller-20261021/sdk-implicit-cleanup/` now checks
**actual implicit compiler destruction**, rather than the explicit typed Drop
continuation. The checked wrapper moves its actual guards and owners into an
uncontracted callee; the callee returns and its actual parameter cleanup occurs
before the wrapper postcondition. No ManuallyDrop, explicit Drop helper or
verified/model callee stub occurs in either checked function. Only the same
qualified std dealloc → actual frozen BumpAllocator dealloc dispatch remains.

`sdk-implicit-cleanup-frame-check-v2`: exit0,1856 non-cover checks all pass,
2/2 covers,103.742s,6322008KiB RSS,zero swaps; optimized one job with fresh
6G/8G/Swap0 admission. #print axioms N/A. An independent saved GOTO fragment
confirms exactly the five native destruction roles/types in order: reply Vec,
proof Ref, statement Box, public Ref, checkpoint RefMut. Its exact prepared
GOTO hash matches the checked target. Metadata inspection exit0,.169s,
46732KiB RSS,zero swaps,1G/2G/Swap0. Contract instrumentation declarations/dead
records are listed explicitly; no unknown call is silently filtered.

This removes the explicit-Drop-helper requirement from the focused cleanup
frame. The original native suffix and this actual implicit suffix have the
same typed destruction order. Moving the live values into that source-step
instance, admitted runtime-layout completeness, allocator dispatch and
whole-caller common execution remain explicit; operation-order equality is
not promoted to a universal compiler-correctness theorem.

The first implicit attempt (`...check-v1`) failed its postcondition:
exit1,41.633s,1779836KiB,swap0. Its probe ran before function-parameter
cleanup. Moving destruction inside the checked wrapper corrected that proof
boundary; this is not a shipped-defect claim. The stronger combined copy plus
implicit-cleanup check timed out: exit1,203.523s,6545012KiB,swap0. It is excluded
and will not be rerun unchanged or with a higher cap. The separate exact copy
frame, actual implicit cleanup frame, actual SDK geometry and existing kernel
frame composition are the retained route. No new whole-copy theorem is claimed.

`python3 tools/s126-sdk-modular-20261021/check-implicit-cleanup-packet.py`
audits all source hashes, regeneration, receipts, exact metadata/stubs,
dependency reuse and compiled cleanup fragment without solver replay. No
binaries are distributed. Failed initial parser inspection was corrected to
recognise and list DFCC instrumentation; it reused the saved dump, with no
second GOTO invocation or proof replay. Initial and corrected parser sources
are retained. Whole S2, S1, S6 and the 100-bit target remain OPEN. No source
adoption decision or production change was made or requested here.
