# KMZ re-verification finding

**7 CONFIRMED, 0 FAILED, 9 OPEN. Checkpoint/append leaf credit remains SUSPENDED.**

All five prior confirmed rows satisfy **CONTROLS FAILED AS REQUIRED (credit stands)**. No control passed, and no original assertion was falsified. Two additional rows close: `LPm_K001` and `LPe_K016`. The remaining nine rows have explicit runtime gaps; a Lean model alone receives no heap-window credit.

This is the authoritative disposition; stage notes retain historical intermediate states. K/L/R numbers below use the KMZ_ prefix. Exact per-row positive/control lists are in [KMZ_ROW_CREDITS.json](KMZ_ROW_CREDITS.json), and all 135 attempts are indexed in [KMZ_RUNS.json](KMZ_RUNS.json).

## Per-original-harness disposition

| Original / harness | Result | Evidence and exact remaining split |
|---|---|---|
| LPn_K001 / LPn_step_frame | **CONFIRMED** | KMY_K006 copy16 control K002 failed; KMY zero-fill and metadata gates are copy-independent. R001 concrete witness. Existing KMY window/expand composition retained. **CONTROLS FAILED AS REQUIRED.** |
| LPa_K015 / LPa_view_inactive | **CONFIRMED** | KMY_K018 copy32 control K003 failed; decoder/indexed-byte K072 and decoder-boundary K073 need no copy control. R002 witness. Existing KMY view-input translation retained. **CONTROLS FAILED AS REQUIRED.** |
| LPb_K016 / LPb_wide_six | **CONFIRMED** | Codec/limb controls K004/K005; six heap-stage controls K007/K008/K029/K010/K030–K031/K012; capacity32 K027 (combined schedule also controlled by K028). R003/R004 witnesses, existing six-window/length laws. K030/K031 replace the timed-out stage4 control with prefix/appended windows. **CONTROLS FAILED AS REQUIRED.** |
| LPe_K005 / LPe_wide_six | **CONFIRMED** | Same shared controlled six-value windows as LPb_K016; identical selected original assertions. No redundant whole-harness replay. **CONTROLS FAILED AS REQUIRED.** |
| LPm_K001 / weights_iterator | **CONFIRMED** | Typed64 inside/frame positives K032/K034, controls K033/K035; empty/last/interior/suffix positives K036/K038/K040/K042, controls K037/K039/K041/K043. L048 composes typed value/frame, empty/interior length, item and retained-suffix relations over KMY/KMX laws. |
| LPm_K003 / selected_reference_write | **OPEN** | Scalar16 codec is controlled (KMY_K017/K006); L053 proves the symbolic growth/value/bound relation. **UNRUN:** constructor and arbitrary prefix, successful growth at len=712+16*i, i<64, through1720, bound to the same selected shared reference and native put_k call. Exact draft: drafts/KMZ_selected.rs. |
| LPm_K004 / append32 | **OPEN** | Raw32 copy KMY_K018/K003 controlled; L049 model closed. **UNRUN:** initial heap prefix and reserve/reallocation windows at every len<=1704, cap=len initially, including retained prefix and appended32. Shared draft: drafts/KMZ_append32.rs. |
| LPm_K005 / query_word_append | **OPEN** | Limb/shift window KMY_K012/K005 controlled; L050 model closed. **UNRUN:** initial prefix and Vec growth for every len<=1732, preserving the original u32 little-endian byte formula. Draft: drafts/KMZ_append4.rs. Legacy KMY_K015 is not independently re-credited here. |
| LPe_K016 / LPe_digest_prefix_cut | **CONFIRMED** | Clone16 K044/K045; heap transitions (16,16), (48,48), (80,96) K046/K047, K048/K049, K050/K051. Each positive checks prefix association, final bytes, length and capacity; every control fails. L054 explicitly composes all three successful retained-prefix reallocations. KMY_K034 oracle chronology retained. |
| LPe_K017 / LPe_roots_queries_cut | **OPEN** | Roots K052/K053 and K054/K055 controlled. Query0 K061/K062 and query16 K065/K066 controlled. L055 and all22 query capacity/value models pass. **TIMEOUT:** i=1..15, cap128 (K063/K064), and i=17..21, cap256 (K067/K068). Next split: actual Vec::from(array128/256), truncate(64+4*i), append4, live-prefix/new-byte checks, then identical controls. Both direct-constructor drafts are UNRUN. |
| LPe_K019 / LPe_semantic_z_cut | **CONFIRMED** | Scalar codec K006; all14 distinct semantic/z stages controlled by K013–K026; capacity16 K028. R005 witnesses. KMY_K051's five selected positive harnesses are individually matched, with no duplicate positive replay. Existing semantic/z length224 composition retained. **CONTROLS FAILED AS REQUIRED.** |
| LPf_K027 / LPf_checksum_projection | **OPEN** | Exact owned1736 Vec::from(array) K059/K060 controlled; oracle KMY_K035 retained; L056 and11 prefix-growth model chunks pass. **TIMEOUT K069/K070:** retained1736-byte prefix during append32/reallocation, cap1736->3472. Next:11 prefix byte windows [160*w,min(1736,160*(w+1))), w=0..10, plus appended32, each with its matching control. |
| LPi_K012 / put_k_arbitrary_prefix | **OPEN** | Scalar codec KMY_K017/K006 controlled; L051 model closed. **UNRUN:** heap initialization and successful append16 growth for arbitrary len<=1720 under the original qbytes auxiliary contract. Draft: drafts/KMZ_append16.rs. |
| LPi_K013 / put_e_arbitrary_prefix | **OPEN** | Canonical WideExact codec KMY_K011/K004 controlled; L052 model closed. **UNRUN:** initialization and successful append32 growth for arbitrary len<=1704, retaining the original auxiliary serializer scope. Shared draft: drafts/KMZ_append32.rs. |
| LPi_K017 / joined_digest_cut_small | **OPEN** | Initial owned-body K059/K060 controlled; KMY_K036 oracle/metadata and raw32 control K003 retained. L058 composes both root replacements with successful prefix growth and checksum append. **TIMEOUT K069/K070:** final append's retained1736-byte reallocation window. Same11 prefix windows plus appended32/control splits as LPf_K027 remain. |
| LPi_K018 / joined_digest_cut_physical | **OPEN** | Same controlled initial body and L059 composition; KMY_K037 preserves physical57607/1880 oracle arguments. **TIMEOUT K069/K070:** same retained-prefix reallocation windows as LPi_K017. |

The five UNRUN arbitrary-prefix/shared-reference rows were not tested after the smaller query and shared1736-byte windows consumed the remaining Kani budget. Their models are complete; actual heap gates and controls remain necessary. [KMZ_UNRUN_SPLITS.json](KMZ_UNRUN_SPLITS.json) gives source hashes, exact domains and next steps. No UNRUN draft or TIMEOUT earns credit.

## Leaf credit

- `compact::expand_values`: **RESTORE / credit stands**, controlled LPn_K001.
- `verifier::candidate::wide_view`: **RESTORE / credit stands**, controlled LPa_K015.
- Both selected prepared-claim serializer properties: **RESTORE / credit stands**, controlled LPb_K016 and LPe_K005.
- **Checkpoint/append: KEEP SUSPENDED.** Three of its12 affected properties are restored: LPe_K019, LPm_K001, LPe_K016. Nine remain OPEN as listed above.

## Negative controls and frozen scope

Frozen source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
KMX patch SHA-256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
Exact stub-file SHA-256: `c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9`.

Every new invocation receipt records both KMX hashes. [KMZ_LEGACY_CREDIT.json](KMZ_LEGACY_CREDIT.json) supplies22 immutable-positive receipt links with both hashes and their new matching controls; old KMY evidence was not edited. No new copy stub was written. Profiles, domains, unwind, exact KMX definitions and auxiliary scope match within each positive/control pair. Stage4's timeout is replaced by the two prefix/appended selected-byte domains, whose union is the original domain.

Every completed control has exactly one failed check: the deliberately wrong asserted byte/word, empty-result boolean or capacity expectation. XOR1 on the asserted byte is equivalent to XOR1 on its expected value. For byte/word controls, all-zero inputs give actual/correct value0 and deliberately wrong value1; canonical WideExact zero and arbitrary-bit QM31 zero satisfy the original domains. The empty-iterator control compares true against false; the capacity controls compare32 against33 and16 against17. [KMZ_CONTROL_WITNESSES.json](KMZ_CONTROL_WITNESSES.json) supplies explicit chosen assignments and failed checks for all43 completed controls. Native R001–R005 replay Stage1 byte/capacity witnesses and the correct relations using unchanged KMX definitions. K029/K010/K012 also retain solver-exported concrete playback values. Native allocator internals are native, so those replays corroborate witnesses and do not replace stubbed Kani heap evidence. See [KMZ_STAGE1.md](KMZ_STAGE1.md).

Kani0.67.0/CBMC6.8.0, opt-level3, CARGO_NET_OFFLINE=true. The existing KMY_src scratch crate contains the copied frozen Cargo.lock; the hash was independently matched to git's frozen blob. Every Kani/native gate validates the resolved package/edge graph against that lock before invocation and records the unchanged lock hash after. No second corpus, crates/ or programs/ edit, wallet/key operation, external message or push.

These results concern the original selected assertions under their original auxiliary stubs/assumptions and the validated KMX copy-value scope. They establish neither unrelated release-function properties nor a general Rust-to-Lean compiler refinement.

## Formal release result and budget

**KMZ_L060 / KMZ_Final.lean PASS**: exit0; wall 0.9844585760147311 s; peak RSS 771412 KiB; swaps0; execution source revision `e31e1f38cd8390ff76e50958021bd03a8eb216d0` (dirty sources archived by hash); target SHA-256 `8fac1ef357def8a98e9db988353ad6b3da802bd9df93046decca0fe99835b547`. Proof-source commit: `c16685617f04f67d3e6a23f15954382bc7d691e1`. Exactly one final manifest replay, after focused targets passed. Its 57 axioms lines use only propext, Classical.choice and Quot.sound. [Final receipt](KMZ_L060/receipt.json), [stdout](KMZ_L060/stdout.log), [time](KMZ_L060/time.log).

The final manifest imports 57 focused modules:38 generated named symbolic window applications and19 handwritten inputs/bridges. The generic growth lemma compiled first, followed by affected chunks and row bridges. No large concrete recurrence was normalized. The generator's --check validation and changed-source hashes are retained in [KMZ_LEAN_PREFLIGHT.json](KMZ_LEAN_PREFLIGHT.json). Failed L008 (reflexive equality simplified to True) and L057 (reserved identifier prefix) remain uncredited; corrected L009/L058 pass. Two duplicate length audits were omitted to keep the final manifest within budget; corresponding KMY length laws remain unchanged.

**Budgets fully used: Kani70/70, Lean60/60, optimized native Rust5/5.** Kani:15 positive PASS,43 failing controls,10 TIMEOUT,2 own option/filter errors. Lean:57 focused PASS plus one final PASS,2 failed drafts. Rust:5 optimized concrete-witness PASS. The two Kani errors were K001's literal dollar-sign filter and K009's missing unstable playback flag; corrected inputs use new attempt IDs. Timeouts were never rerun unchanged or with a larger cap. There is no original-property FAILED row requiring native counterexample replay.

All 135 admitted attempts have exact command, exit status, wall time, peak RSS, swap, source revision/hashes and axioms result in their receipts. Maximum observed RSS:3943984 KiB; all swaps0. Every scope enforces MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64, one own scope at a time. Admission requires allowed:true AND exit0. L021 waited one prescribed180-second retry for contention. [KMZ_ADMISSION_AUDIT.json](KMZ_ADMISSION_AUDIT.json) records actual retries; L021's inherited receipt retry field0 is corrected by that supplemental audit and its retained barrier logs. No launch bypassed refusal.

## Reproducibility and cleanup

[KMZ_SOURCE_ARCHIVE.json](KMZ_SOURCE_ARCHIVE.json) indexes every invocation's exact textual sources, including failed versions; all referenced hashes were verified. Unchanged KMY source snapshots are referenced rather than recopied. The persistent cache `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028` is retained, with baseline pins unchanged and58 new proof objects retained. [KMZ_CLEANUP.json](KMZ_CLEANUP.json) confirms no live own host process and removal of the owned native binary. Attempt-owned Kani temporary directories were removed; shared/unattributed temporaries were retained. No cache was deleted.

Own local queue pauses recovered K035/K058 read-only after submitted scopes ended; no resubmission. The later pause resumed the already-submitted K067 unchanged. The false timeout-label bug that matched a printed command option was corrected by auditing actual summaries; it caused no proof rerun. Own incidental import bytecode was removed, restoring the baseline directory; no baseline source changed. Final tracked changes are confined to this evidence directory. No further formal or runtime regression was run after the single successful final manifest.
