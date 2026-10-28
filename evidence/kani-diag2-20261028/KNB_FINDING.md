# K042 observer diagnosis — work in progress

Classification **(b)**: Kani reports a false failure. The original NBZ symbol reproduces `obs.is_none()` failure; its exact concrete input passes native optimized execution of the same carrier harness and explicit observer stub. Cause attribution/minimization is still in progress; this is not a completed release finding.

Configuration comparison: [KNB_CONFIGURATION.md](KNB_CONFIGURATION.md), immutable snapshots, prefix-normalized full diff, and per-file hashes. The positive harness is identical modulo prefix. Both historical attempts apply all six KMX copy/allocation replacements, unwind 4096, Kani 0.67.0, default solver (documented CaDiCaL; historical executable hash absent), matching frozen lock/graph and optimization settings. NBZ adds negative controls and module declarations.

| Attempt | Configuration | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| KNB_K001 | K042 body renamed KNB; all KMX; playback print | 0 | 80.240347 | 2765792 | 0 |
| KNB_K002 | Original NBZ body/symbol; all KMX; playback print | 1 | 72.182525 | 2757104 | 0 |
| KNB_K003 | Original NBZ, all six KMX registrations off | 1 | 65.569965 | 2757840 | 0 |
| KNB_R001 | Exact K002 failure choices; actual carrier types; explicit mark stub; native release | 0 | 92.777840 | 552648 | 0 |

All have capped receipts recording source revision ccc21aae3bac40353431f55fec844cca9c69166b (dirty experimental inputs captured/hash-pinned), exact command, limits, and N/A axioms. Each passed a separate frozen-graph gate; all post-run lock hashes match 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.

K002 reproduces 1/274 failed, 3/4 covers, failing only `obs.is_none()` at NBZ_native.rs:497 in the verifier::mark replacement. Counterexample: i=2, k=3, j=63. The generated Kani playback test is [KNB_K042_playback.rs.txt](KNB_K042_playback.rs.txt); 533 primitive byte vectors (3176 bytes) are retained in [KNB_counterexample.json](KNB_counterexample.json). The optimized native replay [KNB_playback.rs](KNB_playback.rs) decodes every primitive in order, validates the assumptions and full consumption, uses actual project carrier types, and substitutes `mark` explicitly so the failing observer assertion is exercised. All original assertions pass. The decoder accounts for Kani's primitive-wise array generation, not a guessed whole-array layout.

Affected credit: NBW_K026 return-carrier credit remains OPEN. NBZ_K007 fails the same observer assertion and therefore is not a clean control for its intended false weight property. No result here restores either credit or proves a shipped Rust defect. K003 removes all six KMX registrations and reproduces the same sole observer failure (1/274, 3/4 covers). KMX is not required to trigger this failure. Minimal reduction remains in progress; there is no evidence here for revoking every KMX-based credit.

Recommended interim handling: quarantine this observer-dependent carrier credit, preserve existing KMX validation separately, and do not treat a prefix rename that passes as a repair. No Lean replay is justified before the tool/harness cause is established.
