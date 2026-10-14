# Unified endpoint and early-prefix evidence

This bundle records the initial and rho decoder cases at the exact FS2
interface, the initial sampler law, the union collision bound, and typed
prefix recovery before rows 1 through 26. It is not a full decoder dispatch,
`Inj3`, numerical R1 security theorem, source refinement or privacy proof.
See [the exact scope](../../UNIFIED-ENDPOINTS.md).

Base revision: `3dc5b64deae6c3f41cc7bebf59be0fcaf61a96ce`.

All ten final focused targets passed. There are 28 preserved attempts:
18 failed iterations and ten final green targets. Each attempt has its exact
source snapshot, source hash, compiler output, receipt and timing record.
The final checkpoint passed on its first attempt in 1.49 s, at 3,528,604 KiB
peak RSS, with zero swap. Its 20 axiom reports and all 37 successful reports
across the final targets contain only `propext`, `Classical.choice`, and
`Quot.sound`. No unfinished-proof axiom appears in a final result.

| Target | Final attempt | Wall time | Peak RSS (KiB) |
|---|---|---|---|
| `R1UnifiedFramework` | `f` | 0:01.58 | 3546240 |
| `R1UnifiedRhoCase` | `d` | 0:01.60 | 3550568 |
| `R1UnifiedCollision` | `b` | 0:00.85 | 1812488 |
| `R1UnifiedInitialReads` | `d` | 0:01.55 | 3545852 |
| `R1UnifiedInitialDecoder` | `c` | 0:01.58 | 3551572 |
| `R1UnifiedInitialLaw` | `b` | 0:01.51 | 3543412 |
| `R1UnifiedInitialCase` | `b` | 0:01.54 | 3549612 |
| `R1UnifiedSemanticRecords` | `a` | 0:01.50 | 3537944 |
| `R1UnifiedSemanticRecovery` | `c` | 0:01.65 | 3550728 |
| `R1UnifiedEndpointCheckpoint` | `a` | 0:01.49 | 3528604 |

Every job uses the pinned NUC workspace/cache in its own 4G/6G/0-swap scope,
with Lean limited to 5000 MB and 128 cgroup tasks. Root inspected the final
statements and proof bodies and audited the evidence. `ROOT-VALIDATION.json`
records source/receipt/sidecar agreement for every attempt, matching resource
and timing records, exact current final-source hashes, the ten archive
members and their hashes, and the unchanged 14 central runtime fingerprints.
The final checkpoint was run once after the focused dependent targets passed.
This is a focused cache-based component verification, not a cold historical
manifest replay. No runtime source was changed or runtime regression repeated.

Archive SHA-256: `3ed97bc9be654a54362e6a2ae707c95965a6269b11d5a6805e0deb3936a9ff9a`.

`SHA256SUMS` seals every other file in this directory. The archive contains
only the ten final compiled objects; no loose `.olean` files are included.
