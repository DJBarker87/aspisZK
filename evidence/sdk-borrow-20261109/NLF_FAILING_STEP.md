# NLF failed steps

Target not yet established. L002 failed on record eta and an unavailable erase
lemma; L003 replaces it with structural cases and List induction. L004 failed
on nested-match layout, fixed at L005. L006 needed match reduction before
release rewriting, fixed at L007. L008/L009 rebuild after byte/key carriers
were made explicitly UInt8 lists. No timed-out or memory-killed shape retried.

The native queue K007–K029 encountered one missing closure parameter type in
metadata_control (m.wrapping_add(1)). It compiled the full crate before selecting
each harness, so 23 queued targets were rejected before verification. These
are NOT failing controls or native evidence. The queue incorrectly continued
on compile rejection; this consumed 23 attempt IDs. This is an owned runner
error. NLF_native now requires both 'Checking harness <exact target>' and a
final verification verdict, stopping on preflight/compile/no-verdict outcomes.
The type is now explicit u64. K030–K032 reached verification after the type correction was written; they are recorded by exact source hash, not retroactively counted as compile failures. Native allowance remains 28 attempts; the
remaining wrapper members will be grouped by real shared call dependency.

The native seed initially tried UTF-8 on a frozen binary source input. It
launched no scope. NLF_native_seed now transports every frozen file as base64,
validating the same pinned hashes before and after the copy.

Further focused Lean elaboration repairs are recorded in their raw attempts:
L010 used reserved `meta`; L012 lacked a Decidable instance for the explicit
live-token test; L014/L015 substituted away a Nat binder; L018 needed Invariant
unfolded; L026 needed spaced Unicode comparison tokens; L028/L029 qualified the
SDK release name and removed an already-reduced rewrite; L031/L039 needed
Int.ofNat_eq_natCast for symbolic integer arithmetic; L048 used an over-broad
split on the release match; L050 used reserved `prefix`; L051/L052 needed an
explicit source-state projection and the direct next-token equality. Current
files compile and have standard raw axioms. Failed olean candidates are never
used for credit. No timeout, memory kill, cap increase or extraction occurred.

K051 rejected ScalarReply's stub_verified calibration before checking the
harness because Arbitrary was missing. K052 adds that derive under the SAME
function name and genuinely fails the unimplied assertions. It is not a renamed
verdict. K053 detects the modifies violation and K054 proves the effect contract.

Harness packaging is now NLF_native_packets.patch plus exact receipt-input
archives; standalone evidence .rs/.rs.txt staging files were removed. The patch
contains only cfg(kani) crate attributes/module declaration and the new harness
module. Its final SDK harness bytes equal K060's source hash. This is packaging,
not a Rust logic change or an excuse to repeat a native gate.

Owned runner metadata repair: early native receipts inherited the formal
runner's generic expected_time description. Their exact native argv, frozen
graph, optimization environment and target remain recorded. Future owned
runner receipts now describe optimized Rust compilation plus the exact CBMC
target; old raw receipts are retained unchanged. No arithmetic release gate,
field multiplication, SBF rebuild or dependency build was run here.
