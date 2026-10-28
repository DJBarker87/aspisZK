# KMY window re-verification finding

**5 CONFIRMED, 0 FAILED, 11 OPEN.** Restore the suspended credit for `expand_values`, `wide_view`, and the two prepared-claim serializer properties. Keep checkpoint/append leaf credit suspended: one of its twelve affected properties is restored, eleven remain open.

Frozen source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Copied frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Pinned Kani 0.67.0 / CBMC 6.8.0, optimized standalone gates, offline graph validation before every invocation and unchanged lock hash afterwards. All changes are scratch/evidence only.

## Per-harness disposition

K/L numbers below mean KMY_Kxxx/KMY_Lxxx. Full original names, source hashes and copy inventories are in [KMY_ORIGINALS.json](KMY_ORIGINALS.json). A model theorem alone is never counted as confirmation of a still-unverified heap window.

| Original / harness | Window and runtime evidence | Lean composition | Result and exact remaining split |
|---|---|---|---|
| LPn_K001 / LPn_step_frame | K006: arbitrary-source copy16, arbitrary offset in 96 arbitrary bytes; K007: zero16/frame; K008: original pointer/end/length premises | L002 LPn_step_frame; final expand | **CONFIRMED**. Exactly the original two-window byte formula, return guard and pointer assertions. |
| LPa_K015 / LPa_view_inactive | K018: arbitrary copy32/frame; K072: decoder on every 32-byte input; K073: exact view body with a decoder boundary, both error/success branches and every original pointer/length assertion | L005 translation, L008 read_window32/decode_window32; final view_input | **CONFIRMED**. Pure decoder receives exactly source bytes; runtime boundary covers every possible decoder result. |
| LPb_K016 / LPb_wide_six | K011/K012: actual serializer and limb windows; K040–K045: six heap append32 stages with arbitrary prefixes and independent arbitrary canonical input; K074: capacity schedule | L003 wide_six, L007 six_lengths; final six_wide | **CONFIRMED**. Original length192 and raw[j/32][(j%32)/4] byte projection. |
| LPe_K005 / LPe_wide_six | Same shared 32-byte serializer/append stages as LPb_K016; no duplicate whole-harness replay | Same shared six-window and length theorems | **CONFIRMED**. Original assertions are identical on the selected input domain. |
| LPm_K001 / weights_iterator | Actual 64-QM31 (1024-byte) copy window: K028/K032 TIMEOUT; iterator continuation K033 TIMEOUT | L006 weights_copy_value only | **OPEN**. Typed 64-element window including exterior frame, then iterator empty/last/interior item and retained-suffix contracts. K064/K067–K069 are unrun drafts, not evidence. |
| LPm_K003 / selected_reference_write | K017: actual arbitrary-bit scalar serializer window16/frame | L006 selected_reference_write; L007 prefix bound/value/growth laws | **OPEN**. Heap constructor/prefix window and growth at len=712+16*i, i<64, through1720; bind that heap state to the selected shared-reference call. |
| LPm_K004 / append32 | K018 local32 PASS; full-parent1768 window32 K014 TIMEOUT | L006 append32; L007 prefix/growth laws | **OPEN**. Constructor/prefix and successful reserve/reallocation windows for every len<=1704. |
| LPm_K005 / query_word_append | K012 limb/shift window4 PASS; K015 arbitrary-offset window4 over all1768 bytes PASS | L006 query_word_append; L007 query bound | **OPEN**. Initial prefix and Vec growth for every len<=1732; copying the four appended bytes is closed. |
| LPe_K016 / LPe_digest_prefix_cut | Copy16/32 components; K034 exact two-call Ordered oracle PASS | L006 digest_prefix_cut; L007 append/retained-prefix laws | **OPEN**. Three raw-byte heap transitions (len,cap)=(16,16),(48,48),(80,96), including clone16/prefix association. K075 is an unrun prepared split. |
| LPe_K017 / LPe_roots_queries_cut | K018 raw32 and K012/K015 word4 windows PASS | L009 actual two root windows plus22 query windows, exact152-byte formula | **OPEN**. Heap realization of the two raw roots and all22 query appends/capacity cases. K076 is an unrun prepared split. |
| LPe_K019 / LPe_semantic_z_cut | K017 scalar16; K050–K059 and K051's stage10–13 results cover all14 distinct heap stages; K074 capacity schedule | L006 semantic_z_cut; final semantic_z and length224 | **CONFIRMED**. Ten semantic-alpha scalars followed by two (x,y) pairs, each with arbitrary full limb inputs and framed arbitrary prefix. |
| LPf_K027 / LPf_checksum_projection | K018 raw32; K035 exact checksum oracle PASS | L006 checksum_projection; L007 growth | **OPEN**. Initial owned1736-byte Vec window and the retained1736-byte prefix during checksum append/reallocation. Oracle chronology, tag/length and returned answer are closed. |
| LPi_K012 / put_k_arbitrary_prefix | K017 actual scalar16/window PASS | L006 put_k_arbitrary_prefix; L007 bounds/value/growth | **OPEN**. Heap initialization and growth for arbitrary len<=1720, under the original qbytes auxiliary contract. |
| LPi_K013 / put_e_arbitrary_prefix | K011 actual canonical WideExact32/window PASS | L006 put_e_arbitrary_prefix; L007 bounds/value/growth | **OPEN**. Heap initialization and growth for arbitrary len<=1704; original auxiliary serializer scope retained. |
| LPi_K017 / joined_digest_cut_small | K018 raw32; K036 JoinedOracle selected-byte/order/arguments PASS, sizes3/5 | L003 joined_digest exact replacement/remainder/answer formula | **OPEN**. Initial1736-byte heap-body association and final append's retained-prefix reallocation window. |
| LPi_K018 / joined_digest_cut_physical | K037 same oracle contract PASS, actual argument sizes57607/1880 | Same joined_digest theorem | **OPEN**. Same initial-body and reallocation windows; physical oracle metadata is closed. |

## Suspended leaves

| Suspended leaf | Credit decision |
|---|---|
| compact::expand_values | **RESTORE**: LPn_K001 closes the sole remaining affected property; earlier KMX-confirmed properties retained. |
| verifier::candidate::wide_view | **RESTORE**: LPa_K015 reconstructed through copy/read/decoder/view composition. |
| prepared_claim serializer | **RESTORE** both selected six-value serializer properties, LPb_K016 and LPe_K005. |
| checkpoint / append stages | **KEEP SUSPENDED**: LPe_K019 restored, eleven affected properties still OPEN as above. |

These decisions concern the original selected assertions, with their original auxiliary stubs/assumptions and the validated KMX copy-stub value scope. They do not establish unrelated release-function properties or a general Rust-to-Lean compiler refinement.

## Reconstruction and scope

The copied KMX stubs are unchanged. Direct calls explicitly install the validated loop where optimized attributed calls did not reach it (K004 is excluded from mitigation credit). Frozen field overlays change only module routing and byte-copy calls; [KMY_serializer_sources.json](KMY_serializer_sources.json) records original/overlay hashes. The view boundary retains the frozen body and replaces only the pure decoder call with a checked input/result interface. Layout constants are copied from frozen source declarations.

L002 proves global frame/disjointness and contiguous-window composition. L005 translates local windows to arbitrary global origins. L008 proves equality of all32 decoder input bytes. L003/L006/L007/L009 prove byte projections, append lengths, prefix bounds, to_vec value identity, and successful retained-prefix growth. Actual Vec stages retain arbitrary prefix bytes, rather than assuming a zero prefix. Codec checks retain the originals' full canonical WideExact domain and arbitrary-bit QM31 domain. Capacity schedules are checked by K074; capacity is used only as a split interface, not an added original assertion.

## Execution accounting and failed drafts

**Kani budget: 60/60 conservatively** =56 admitted invocations (including all setup/compiler failures) +4 extra harnesses selected by K051's substring match. K051 selected stages1,10,11,12,13 and all five passed. K060/K061 redundantly completed stages10/11 while that selection was being inspected; both are retained and counted. K062/K063 were deferred and their already-complete K051 evidence reused. No further Kani launch is authorized by this budget. K075/K076 and the typed-window/iterator drafts are unrun.

K001 had an unsupported own command option; K003 an omitted own PATH entry. K016 failed only a66-element initializer unwind with bound65; every value check was undetermined. The corrected typed window and its limb split timed out. K065/K066/K070/K071 failed before verification because our constant extraction omitted FIXED; corrected K072/K073/K074 passed. L001/L004 were failed Lean drafts, corrected by L002/L006. No original byte/property counterexample occurred, so there is no FAILED row or native counterexample replay; Rust runs0/5.

All timeouts and failed drafts remain in the receipts. No timeout is interpreted as a counterexample or PASS. The replacement shapes and remaining obligations are explicit above. [KMY_STAGE_NOTES.md](KMY_STAGE_NOTES.md) retains historical progress notes; this file is authoritative.

## Reproducible evidence

Every attempt has its exact command, source revision/hashes, exit status, wall time, peak RSS, swaps and axioms output in its receipt/stdout/time logs. [KMY_RUNS.json](KMY_RUNS.json) indexes them. Source snapshots are deduplicated by SHA-256 in sources/ and indexed by KMY_SOURCE_ARCHIVE.json. Only accepted propext/Classical.choice/Quot.sound axioms receive proof credit; failed drafts' sorryAx diagnostics receive none.

Every admitted scope uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, one scope at a time, after reservation JSON allowed:true AND exit0. Maximum recorded RSS:6473584 KiB; all recorded swaps0. Frozen dependency graph validation and before/after lock hashes are retained per gate. No shared launcher repair, release-source changes, wallet/key changes or push. Persistent cache `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028` is retained.

Final manifest: **KMY_L010 / KMY_Final.lean PASS**, exit0, wall 0.769491s, peak RSS 768460 KiB, swaps0, source revision `926033a26f4120db398c60dbd9a0986617a907e4`, source SHA-256 `07dec3f73d3aa54afdf104d2ccc9710ef65c42fdb23a8e58b18b1a0dc496c13f`. Thirteen axioms audit lines contain only accepted axioms (or none). Selected cached objects were hash-verified before the single final import/bridge replay. No unchanged final replay was run.

Final budgets: **Kani60/60 conservative units, Lean10/60 compiles, Rust0/5 runs**. The 56 Kani invocation receipts comprise37 successful invocations (K004 excluded from mitigation credit),12 timeouts,1 initializer-unwind failure and6 setup/compiler failures. K051 adds four successful selected harnesses to the conservative budget. All14 semantic/z stages are green; K060/K061 are counted redundancies, not additional proof strength.

[KMY_CLEANUP.json](KMY_CLEANUP.json) confirms no live own process and eight unchanged retained cache objects. The driver had already removed generated object scratch (zero remained for explicit removal); no owned external-solver temp was identified. Shared/unattributed solver files were retained. The source archive contains32 unique textual snapshots for66 attempts, with no binaries or .olean files committed.
