# D438: allocator black box applied; outside-box foreign-call obstruction

V229 and V230 remain **SUSPENDED under own-1**. This is a negative
qualification check, not a positive complete-cone purity proof, a privacy
counterexample, or an assertion that the allocator reads witness data.

The checker treats alloc/realloc/dealloc and **everything they execute** as
the black box. All four inherited allocator witnesses are withdrawn:
initialization byte, tcache TLS, `__libc_single_threaded`, and errno save/restore.
No ownership classification of those data is used in this check.

## Exact outside-box witness

The pinned release-configured original statement functions reach:

1. V230 -> V229 (`0x18ca5`, relocation `0x5d170 -> 0x18a50`).
2. V229 -> forest schedule builder (`0x18a64`, `0x5d250 -> 0x18dd0`).
3. Forest builder -> legacy schedule builder (`0x18df3`, `0x5d218 -> 0x19620`).
4. Legacy builder calls `endpoint_counts(&links)?` at frozen source
   `crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs:242`.
5. The inlined `endpoint_counts` initializes `producers` and `consumers` as
   `[0u8; 1024]`, source lines249–250. In this release cohort it loads
   `memset@GLIBC_2.2.5` from GOT `0x5d240` at `0x19b59` and calls it at
   **`0x19b67` and `0x19b79`**, with zero fill and length`0x400` each.

These calls initialize stack arrays in the caller. They are not descended
from an allocator entry, do not allocate a block, and are not allocation
failure handlers. The calls occur before the endpoint-counting loop; the
captured successful original-root executions pass this initialization stage.
The forest builder has another pair at `0x191ac` and `0x191bb`.

Thus the exact conjunction demanded by own-2''(a) fails its **foreign-call**
clause in the original-root release cohort. No exemption for libc memory
primitives was supplied. This report does not assume one, enlarge the
allocator boundary to include unrelated libc calls, or claim a mutable read
inside `memset` without examining its resolved implementation.

The probe also has memcpy/memmove imports; import presence alone is not used
as a reachability witness. Cleanup/unwind paths are likewise not needed for
this successful-path obstruction. It is not necessary to inventory every
other callee to reject a universal no-foreign-call condition once this
specific call is established. No positive complete-cone result is claimed.

## Scope and reproducibility

`tools/pv-owng-20261029/static-check.py` revalidates 44 complete inherited
source files (including their six tracked application/configuration blobs),
the release rlib, probe source, feature/profile inventory, Cargo.lock and
probe binary:49 host files total. It reruns read-only objdump/readelf/rustc
identity inspection and requires byte equality with the captured output.
It checks root relocations, call instructions, memset dynamic relocation,
size and source array initializations. `check-output.json` records exit0.
`static-capture.json` pins both input captures and retains function excerpts.

The release rlib hash is
`0e0184bcafb0c970d9a2129429578f2fb85e69a844f6e4ddddafbb05f6f5acd0`.
Probe hash is
`b00cc400ee86ecfcdf5104776c89565daa603f97ee60eedb0441caf138785bcb`.
The probe links the unmodified pinned statement rlib with rustc1.94.1,
optimization enabled, debug assertions/overflow checks disabled, panic unwind.
Resolved crate features/profiles and lock hash are in `native-result.json`.
This supports a rejection in the deployed-configuration original-root
cohort; it is **not** an execution of the shipped client artifact.

Read-only `nm -C` inspection of the inherited client finds separately named
`aspis_prover::host_forest` functions. Their source uses a fixed array/flags
implementation, unlike V229's assigned statement Vec/collect/sort/dedup body.
Symbol absence alone would not establish absence of inlined code; no such
absence proof is claimed. We do not substitute those functions for V229/V230
or silently promote the diagnostic probe into a shipped-artifact execution.

Address independence and closure of channel(iii) are **not certified for the
whole cone**. Source-local cursor comparisons can cancel base addresses;
that observation is not a proof for every remaining library/runtime path.
No allocator-internal errno read is used to reject channel(iii).

## Consequences

The own-2 prerequisites fail before its conditional value/exhaustive execution
route can earn restoration. No new named Result literal theorem, Lean-literal
byte comparison, fixed allocation-trace proof, or abort proof is claimed.
The one diagnostic scope and its fingerprints remain measured supporting
evidence. The class **“exhaustive over a singleton input domain, deployed
compiled artifact” is not assigned**. This is not a source-binding proof.
The existing own-1 structural route and rdea-1 allocator/failure boundary
remain available and retained; V370/D381/D386 remains named.
