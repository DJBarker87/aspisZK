# Narrow ordinary raw-law cache preparation

Metadata preparation passed; this is not a new Lean theorem or a sampler
probability result. No compiler ran during this operation.

`OrdinaryRawMass` needs only `V7Tag73EightRetrySamplerLaw`, whose only missing
predecessor is `V5ComponentCStoppingTimeSampler`. The original FlatRouting
import would add 38 modules and encounter 12 differing native boundary
outputs. None of that larger closure was installed.

Instead, two exact **local** cached source/output pairs were appended to
the existing higher-Y overlay. All sources match borrowed V7 commit
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; both retained local build traces
and olean headers identify Lean 4.32.0 / `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Their 10+4 historical standard-only axiom reports receive no new theorem
credit. In particular, the local stopping-time output `e0185f92…` was used,
not the different native-cache output `07250215…`.

The four already-pinned boundary pairs checked were RejectionSampler,
QM31TowerExact, DeployedDecoderFiberCap, and SamplerDecoderExact. The last
is needed only by the prospective decoder bridge. No boundary source or
output was replaced. Full source/output/trace hashes appear in the
[append receipt](ordinary-raw-cache-append.json).

## Exact mutation and retention

The source continuation parent is
`15700387af1d52af4b7ddff8de92541ec2891ff2`; the inherited runner remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`.

The mutable base manifest had 794 entries. Four entries (two sources and
two oleans) were appended, producing 798. Its existing entries are
unchanged. The immutable FiniteOptionMass v1 run manifest retained all
859 entries verbatim, and all 33 recorded green targets were verified
unchanged. The green state was not promoted into the base manifest or
rewritten; future normal runner snapshots continue to merge it.

The new helper checked all expected hashes and destination absence
before copying. It saved before/after manifests and the prior green
state, and atomically published the new base manifest without modifying
any hardlinked predecessor bytes. The remote operation was guarded
against a concurrently advanced manifest or green state.

Remote staging/retained originals:
`/home/dombarker/project-offloads/aspis-ordinary-raw-cache.gqikCY`.
Active overlay: `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.
Only Tailscale `dombarker@100.108.41.90` was used; `nuc.local` was the
verified host-key alias, never the network destination.

Before base manifest SHA-256:
`46c0485b661719d093fa8392783e36f42f5f446fa95d54525f3e0438ff232ab1`.
After base manifest SHA-256:
`7881b518c94f594a25674ad83e74b22298bcf547567df53b21b6efc5802144cc`.
Unchanged 33-target green state:
`979f1f2d26543b494a62876235b73ee44133da3354c631a88a9ea99feb6a9ecd`.
Unchanged 859-entry run manifest:
`d3a5a4d89c41f017deaee039f799d65dbff84e6d94b81e1dbe2803cb90d8f6e9`.

The new `append_ordinary_raw_cache.py` and `ordinary-raw-cache-*` files
under `experiments/` retain the helper, terminal output, manifests,
green-state snapshot, and local trace snapshots. The older sampler
checkpoint metadata is untouched.

## Next check and boundaries

The first changed `OrdinaryRawMass` leaf, under a separate root compiler
grant, is the actual NUC import-compatibility check. No unchanged package
or large V7 suite was replayed. If import compatibility fails, retain
the failure and consider only the two source-pinned focused exports in
dependency order; do not replace 12 boundary artifacts or raise caps.

`EightRetryDecoderBridge` was verified separately but is **not appended**
by this operation. A later source-shaped block adapter can port the
specific V7 block/word equivalence, total four-block decoder commute,
discarded-word suffix and exact-value lemmas without importing the full
gamma or semantic-transcript modules. The actual nested stopping-tape
coupling and source/random-oracle law remain separate obligations.

Read-only local audit:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_ordinary_raw_cache.py
```
