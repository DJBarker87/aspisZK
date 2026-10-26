# Native query driver inside Prepared::new, 2026-10-26

Target not yet established; no whole S1/S6, SDK or release claim.
Frozen default/devnet source remains4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Only the isolated proof fixture changes. Production verifier source is untouched.

## Checked enclosing claim

The complete native Prepared::new / original prepared_claim point6 harness
now takes its query output from the frozen native eight-pair DRIVER body,
rather than selecting an unrelated query array and selected advance.
All same-caller constructor/claim fields, ordered digest preimages, caller
scratch pointer, 29 gamma powers and claim continuation are still checked.
The returned queries and rho absorb state are compared with that SAME actual
driver return. Query rejection maps to the actual Transcript error and leaves
incoming scratch unchanged. Native complete constructor success is covered.

Implementation detail: a cfg(kani) function twin has exactly the frozen
queries_from_pairs body, changing only the function name. It uses the SAME
original native QueryScan/default/finish types and helpers. The existing
observational query hook calls this twin, avoiding recursive substitution of
its own Kani stub. Full native errors and buffers are retained. This is not
an opaque carrier or simplified driver. The source checker compares the
complete twin declaration with the frozen function, permitting only the name
change. This establishes no historical compiled-symbol/ELF identity.

Before: queries_from_pairs returned an independently scripted Ok array/state
or chosen error. After: its hook executes the complete native driver, records
its actual output, and lets its actual Ok/Err choose the constructor branch.
One lower boundary remains: QueryScan::scan returns a common bounded complete
22-word-buffer/len/draws/stop state. Its poststate contract is an explicit cut,
not a whole scan proof. Existing sampler/arithmetic/dot normal-return cuts and
scripted digest replies remain. The earlier source/native block packets and
TOTAL source decoder installation are separate evidence, not silently
installed as extra axioms in this native check.

## Validation and scope

Local focused compile-only check s1-native-prepared-query-driver-v1 exited0,
4.526957209s, peak RSS688111616B, observed aggregate713752576B, swap0. The
shared local compiler lock and4GiB guard were used; no local solver ran.
The previous source-preparation exact-match guard failure is retained in
s1-native-query-driver-prepare-v1; no compiler ran in that failed attempt.

Fresh NUC admission and both before-phase admissions passed. One dedicated
12GiB MemoryMax /11GiB MemoryHigh /MemorySwapMax=0 scope ran optimized -j1
compilation then focused Cadical verification with300s solver timeout and
checked unwinding assertions. Verification exited0,153.149522661s, peak RSS
6137532KiB, swap0;3465 assertions passed.2/3 covers are satisfied: query
rejection and complete constructor success. The point6 claim-push-error
cover is deliberately unreachable because point6 completes all174 pushes;
earlier point5 claim-error evidence remains separate and is not replayed.
No cgroup high/max/oom/oom_kill event occurred. No cap was increased.

All exact source/tool/command/pre-post/cgroup pins, the contemporaneous source
snapshot and terminal logs are source-only in:
- evidence/s126-current-caller-20261021/s1-native-prepared-query-driver-v1
- evidence/s126-current-caller-20261021/s1-native-query-driver-terminal-v1

Audit: tools/s1-native-prepared-query-driver-20261026/check.py.
#print axioms is N/A for Kani; this packet adds no Lean axiom. Native Kani
malloc-success/no-uninit-check interpretation is retained. It does not prove
initialization, concrete allocator behavior, SDK/private heap effects,
abort/drop/cleanup, adaptive-oracle transport or deployed source association.
No source adoption decision or frozen verifier re-pin is requested.

## Next concrete target

Run the same enclosing check with the scan poststate cut removed, so the
complete original QueryScan, word decoder, membership and all native query
loop steps execute. Existing upper sampler/arithmetic/dot cuts remain. That
candidate is not covered by the successful receipt above; it needs its own
focused validation and honest failure/qualification record. Full literal
matching-data / SessionAPrepare identification and shared actual stage1
binding still require their same-source joins; this packet does not close
those or duplicate the lead's S2/import work.
