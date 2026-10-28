# KNA checkpoint/append finding

**0 newly CONFIRMED, 0 FAILED, 9 OPEN. Checkpoint/append leaf credit: KEEP SUSPENDED.**

Execution stopped because the shared local evidence filesystem ran out of space. Fourteen Kani invocations completed; all timed out. No positive or control earns credit. The seven previously confirmed KMZ rows retain their authoritative disposition, including the three restored checkpoint properties; checkpoint remains 3/12 restored.

## Infrastructure stop and unused budget

The existing recovery launcher raised:

```
OSError: [Errno 28] No space left on device: '/Users/dominic/ZK/.worktrees/cx-kani-reverify3/evidence/kani-reverify3-20261028/KNA_K014'
```

The error occurred in `KMY_host.py`, `recover()`, creating the local receipt directory after K014 had finished on the host. K014 was recovered **read-only**, with no resubmission, and classified TIMEOUT from its retained CBMC diagnostic. The interrupted pair index was reconstructed from the two immutable receipts. `/dev/disk3s5` reported 100% capacity; available-space observations fell from 211 MiB to 128 MiB to 117 MiB. No shared storage or launcher was repaired.

The operating file [local-lean.txt](/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt), rule 5, requires: “If the launcher or host misbehaves, stop and report the exact error in one paragraph; the lead fixes infrastructure.” The recovery launcher's storage environment failed. Further launches cannot reliably retain the mandatory evidence. This infrastructure stop, rather than Kani exhaustion, prevents **all** remaining execution, including Lean-only work. [Stop record](KNA_INFRASTRUCTURE_STOP.json), [original traceback](KNA_RUNTIME.log).

**Budget used: Kani14/90, Lean0/40, optimized Rust0/5.** The table below gives the individual under-80% justification and precise remaining work for every row. Prepared Lean and native sources are **UNRUN**, not proof results. No axioms audit, formal release result, or final manifest replay is claimed.

## Per-row disposition and remaining splits

| Original row | Result and completed evidence | Exact next work; individual early-stop justification |
|---|---|---|
| LPe_K017 | **OPEN.** Actual Vec::from(array128), truncate(64+4*i), append4 for i1..15: K001 positive/K002 control TIMEOUT. Actual array256 case, i17..21: K003/K004 TIMEOUT. | Retain those actual constructors. Split live-prefix observation from appended4. For cap128 use live-prefix windows [0,64), [64,124); for cap256 use [0,64), [64,128), [128,148), always constrain j<len. Check constructor association and postappend association in each selected prefix window, plus a separate appended-byte b<4 gate. Every split needs an identical failing control; halve any timed-out prefix window. These replacements and KNA_LPe_K017 are unrun because evidence recovery failed. |
| LPf_K027 | **OPEN.** Shared retained1736 prefix windows [0,160), [160,320), [320,480), [480,640), [640,800): K005/K006, K007/K008, K009/K010, K011/K012, K013/K014, respectively. Every positive and control TIMEOUT. | Halve each of those five 160-byte windows into its two 80-byte windows. Run the six remaining prescribed prefix windows [800,960), [960,1120), [1120,1280), [1280,1440), [1440,1600), [1600,1736), and appended32 [1736,1768), each with control, during actual cap1736→3472 append32. Stop occurred before these launches and before the checksum Lean bridge. |
| LPi_K017 | **OPEN.** Shares exactly the five timed-out positive/control body windows above; prior root replacement/oracle evidence retained. | The identical eleven-prefix-plus-appended32 coverage remains required, using the five parent windows' 80-byte replacements above. Compose with KMZ/KMY root replacement, three oracle calls, length1768 and the exact joined-byte formula for proof/public sizes3/5. Shared heap and KNA_LPi_K017 execution were blocked by the receipt-storage failure. |
| LPi_K018 | **OPEN.** Same shared timed-out body windows; physical oracle arguments remain covered by KMY_K037. | Same precise heap splits as LPf_K027; retain proof/public sizes57607/1880 and the joined-byte/call-count/length relation. Shared heap and KNA_LPi_K018 were blocked by the same infrastructure stop. |
| LPm_K003 | **OPEN; UNRUN.** Prior controlled scalar codec retained. | Run selected shared-reference draft at symbolic i<64, len=712+16*i, arbitrary full prefix, dereference the same selected reference and call put_k once; check construction, growth, length and retained/appended byte relation. Pair with wrong-byte control; split observation windows if needed. Draft and KNA_LPm_K003 were not launched before storage failed. |
| LPm_K004 | **OPEN; UNRUN.** Prior controlled raw32 copy retained. | ONE actual append32 on arbitrary symbolic len≤1704 and arbitrary full prefix, initially cap=len, retaining constructor association, successful growth and exact prefix/appended relation. Matched control required. No enumeration of lengths. Shared draft and KNA_LPm_K004 were blocked before launch by storage failure. |
| LPm_K005 | **OPEN; UNRUN.** Prior controlled limb/shift gate retained. | ONE actual append4 on arbitrary symbolic len≤1732 and arbitrary prefix; compose with the original u32 little-endian shift/byte formula. Check initial prefix, growth, length, retained and new bytes; matched control. Draft and KNA_LPm_K005 were blocked before launch by storage failure. |
| LPi_K012 | **OPEN; UNRUN.** Prior controlled scalar16 codec retained. | ONE actual append16 on arbitrary symbolic len≤1720 and arbitrary prefix under the original qbytes auxiliary contract, with constructor, successful growth, exact limb-byte relation and matched control. Draft and KNA_LPi_K012 were blocked before launch by storage failure. |
| LPi_K013 | **OPEN; UNRUN.** Prior controlled canonical WideExact codec retained. | Shared append32 frame gate for every symbolic len≤1704, then original auxiliary serializer association/canonical domain and exact eight-limb byte projection, with matched control. Shared draft and KNA_LPi_K013 were blocked before launch by storage failure. |

[Machine-readable row credit and remaining intervals](KNA_ROW_CREDITS.json). Original unrun draft hashes and domains remain in [KMZ_UNRUN_SPLITS.json](../kani-reverify2-20261028/KMZ_UNRUN_SPLITS.json). No timed-out gate was rerun unchanged. The prescribed halving replacements are explicitly unrun after the infrastructure stop.

## Frozen scope, controls and receipts

Frozen Rust revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

- Frozen Cargo.lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
- Exact KMX patch SHA-256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
- Exact KMX stub file SHA-256: `c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9`.

Both KMX hashes appear in every invocation receipt. No new copy stub was written. Every completed positive/control pair has identical source definitions, profile, domain, unwind and auxiliary configuration except the selected equality's XOR1 expected byte. Both sides timed out; therefore ruling (r') awards no credit. No original assertion counterexample was obtained, so no FAILED row or counterexample replay is claimed.

The existing scratch crate, copied frozen lock, workspace and persistent cache were reused. Each invocation validated the resolved package/edge graph against the lock before running, used CARGO_NET_OFFLINE=true and opt-level3, and recorded an unchanged lock hash afterwards. K001–K004 use the existing default solver setup; K005 onward use installed Kissat and CBMC formula slicing for previously unrun byte-window shapes. Both gate versions are hash-archived; no timed-out shape was retried with a different solver.

[All14 receipts](KNA_RUNS.json) record exact command, exit status, wall time, peak RSS, swaps and source revision; axioms are N/A for Kani. Maximum reported RSS: **3014224 KiB**, swaps **0** throughout. Every admitted scope enforced MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; one own scope at a time. The existing admission wrapper required allowed:true **and exit0**. No admission refusal or transport retry occurred. [Pair audit](KNA_PAIRS.json), [source index](KNA_SOURCE_ARCHIVE.json), [frozen pin check](KNA_FROZEN.json).

The Lean generator passes its textual --check preflight and prepares39 focused symbolic targets plus one final manifest. It includes frame/partition laws, named windows, half-window unions, capacity domains, original limb/word projections, length arithmetic and oracle call counts over KMY/KMZ/KMX laws. **None has been compiled.** The five optimized native witness cases are also unrun. These source preparations do not substitute for runtime heap gates or Lean validation.

[Cleanup inspection](KNA_CLEANUP.json) confirms no live own runner, owned temporary directory, compiled-object scratch or new KNA cache object. The persistent cache was retained. All tracked changes are confined to this evidence directory. No crates/ or programs/ changes, wallet/key operation, external message or push occurred.
