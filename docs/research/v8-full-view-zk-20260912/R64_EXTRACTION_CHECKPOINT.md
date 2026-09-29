# R64 extraction checkpoint — proof not yet compiled

Historical checkpoint: the later [canonical-product arithmetic step](R64_CANONICAL_PRODUCT.md)
compiles the Nat-only draft locally. Artifact retrieval and generated execution
are still pending; the extraction result below is unchanged.

Base `3a3cc6f2e9ae1d34ec2b6933bba686e16c86d722` (R63), branch
`research/v8-r64-guarded-m31-20260929`.

## Executed progress

`tools/extract_r64_field.py` successfully copied the selected R62 field and
its three included arithmetic files **unchanged**, checked all 197 stage
pins, and extracted the dependency closure of a single wrapper calling
`M31::inv`. The tiny extraction crate has no dependencies. No production
source, runtime profile, proof fixture or protocol was changed.

Pinned tools:

- Charon: `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
- Aeneas: `e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813`.
- Rust toolchain: `nightly-2026-06-01`; offline, locked, release, one build job.

Observed completed tool output, **not yet a downloaded artifact audit**:

| Command | Exit | Wall | Peak RSS (KiB) | Swaps |
|---|---:|---:|---:|---:|
| Generate offline lockfile | 0 | 0.04s | 20,592 | 0 |
| Charon extraction | 0 | 1.17s | 214,976 | 0 |
| Aeneas Lean translation | 0 | 0.36s | 67,408 | 0 |

Systemd unit `aspis-r64-extract-a.service` returned success. Its limits were
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. This work spent
time in source compilation and translation, not arithmetic elimination.

Remote output:
`/home/dombarker/project-offloads/aspis-r64-extracted-20260929-a`.
The completed runner reported 11 pinned output files, including the unchanged
source copy, LLBC and generated Lean/translation metadata. **Their bytes and
hashes have not yet been fetched or independently checked locally.**

## Connection interruption and exact resume point

After extraction, SSH over Tailscale stopped responding. Both
`100.108.41.90` and `fd7a:115c:a1e0::c101:29a6` timed out; Tailscale status
still reported the NUC online, but two Tailscale pings received no reply.
The two source-transfer attempts for the next Lean leaf/runner failed.
The subsequent local SSH launch attempt was terminated while connection
establishment remained unresponsive. No successful new Lean compilation
was observed.

On reconnect, **inspect**, do not blindly restart:

1. Check `aspis-r64-bound-a.service` and the existence/content of
   `/home/dombarker/project-offloads/aspis-r64-bound-20260929-a`.
2. Retrieve the already completed extraction's `commands.json`, logs,
   `pins.json`, LLBC, generated Types/Funs and `translation.json`.
3. Verify its source hashes against R62 and inspect all generated declarations
   and any opaque/external dependencies before treating the extraction as
   usable proof input. Do not repeat the successful extraction unchanged.
4. Compile the local **unverified** `CanonicalProduct.lean` draft first in the
   cached R63 workspace, then prove the actual newly generated guarded
   multiply equal to R63's generated multiplication, including fallback.
5. Transfer that equality through the freshly extracted square loop and
   guarded inverse, retaining the zero assertion behavior. Follow with
   word-level CM31/QM31 inverse and sampler composition.

The proof draft and its draft Lean runner remain uncommitted; only the
successfully executed extraction recipe and this accurately limited
checkpoint are committed. This checkpoint is not a formal release result.

## Unchanged boundary

No new Lean theorem, multiplication-equivalence result, full privacy theorem,
soundness theorem or CU improvement is claimed. The first remaining proof is
still the selected guarded M31 execution equivalence. Full shared-oracle,
seed/commitment, observer/transcript, failure/retry/publication and loss-bound
obligations remain, as does separate pre-beta extraction soundness.

Selected complete-execution CU remains **1,497,377 / 1,498,764**. Both actual
1M runs exhaust. No SBF rerun, merge, deployment or wallet operation occurred.
