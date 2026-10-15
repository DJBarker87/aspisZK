# J1 S2 build-configuration reuse inventory

Inspection snapshot: worktree `3c79ec30fa44f408c716bb345050c137e907fa67`.
This inventories the split10 build configuration, its adopted route-guard overlay and retained earlier
P3/v3b records. It is not a source-refinement or security conclusion.

## Split10 baseline and current route-guard overlay

The pre-guard local baseline is the split10 artifact, documented in the
[adoption record](../evidence/split10-adoption-20261015/adoption.json) and the
[frozen build bundle](../evidence/split10-v152-20261015/README.md). Its
measured SBF ELF SHA-256 is
`5a91339444d14c2a9c63c9dbd22923003ebd79f63b76c97da175c2042aa62912` and the
optimized `pool_gate` binary SHA-256 is
`9ba7074f21a758cb2d69d66d8323fb78c0f60a98c981efe1e9e2f7ca265fddeb`. The
adopted baseline source pins are:

| File | Adopted baseline SHA-256 |
| --- | --- |
| `programs/r1-cost-probe/src/lib.rs` | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `tools/r1-cost-probe/src/bin/pool_gate.rs` | `f8986a966a6b17340c84c8d6a3514eed061f25cba8f8d65433d458dc8f379406` |
| workspace `Cargo.lock` | `f93f8f524fdd707c7a3b7feade31d015c891264b6c8fbd8bff885249e19600ea` |
| `programs/r1-cost-probe/Cargo.toml` | `1208d93c95f3e4e769fd1ba48f71bbb031c4ddd33793f09f5cc6405fe9da71f1` |

The build receipt's source revision is
`aba310f1daa065a27da89d15c6c47166037a8a71+shared-point-68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63+split10-294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a-b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4`.
The build selected `pool-adapter,private-leaf-salts` with default
`custom-heap`; `private-leaf-salts` forwards to the verifier crate feature.
The program manifest enables `optimized-terminal` on `aspis-r1-cost-probe`
and `r0,pool-v1-kernel` on `aspis-statement`. The saved build command used
Solana `cargo-build-sbf` 3.1.13, platform-tools v1.52 / SBF rustc 1.89.0,
`--locked -j 2`, and the pinned `cargo-target-v152` cache. Its original scope
was `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`.
The separately compiled host driver used Cargo/rustc 1.94.1, release mode,
`--locked --offline --jobs 2`, and `private-leaf-salts`.

The current worktree has a narrowly changed `lib.rs` route guard at SHA-256
`36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9`.
The focused unit-test evidence is in
[r1-route-guard-unit-20261015](../evidence/r1-route-guard-unit-20261015/).
That overlay has now also been built into a separate SBF artifact and replayed
against the retained split10 fixtures; see
[route-guard replay evidence](../evidence/r1-route-guard-replay-20261015/).
The resulting ELF SHA-256 is
`243a3193f17744d221706edf835fc71e40de914cde90cbadf9dc74108ba5dd19`.
The root has now adopted the route-guard source and this measured local
artifact on the research branch; the former split10 artifact is retained as
the comparison baseline. This is not deployment or security release approval.
See the [root record](../evidence/r1-route-guard-lead-review-20261015.json).
The six replay runs reported the expected successful transactions, lifecycle
rejections, and replay rejection. In each of the five successful transaction
cases, both stage-one and terminal CU were 7 lower than the matching split10
baseline run. The build receipt records cwd `/home/dombarker` rather than the
source snapshot directory; the command nevertheless uses the absolute pinned
manifest path and the source-manifest checks. This is retained as a provenance
detail, with no cosmetic rerun.

## Earlier P3 private-leaf-salts record

The earlier P3 source-only record remains useful history:
[P3 private-leaf-salts evidence](../evidence/p3-private-leaf-salts-20261013/).
Its retained manifest has 571 entries (SHA-256
`a72db26cbb51322499374741dafc13c7681394aa55a6666f156bd068ff25ea1c`) and
archive SHA-256
`64d9da26beda801de373180a94ee2ffbea3cf4e8cd04ab083748b5fe7f1d7604`.
That build's stripped/unstripped ELF hashes were
`c94675d0f0682170ed9288e31feb31c76669f9698c554c36e9978c9a98835ab5` and
`58235db5d3c94dc7fd20eec72152e2470246ce535061949621360a25b98b34e6`.
It is not the current adopted split10 artifact.

## Separate v3b adapter-only comparison

The [v3b feature fingerprint](../evidence/pool-v0/pool-adapter-v3b-feature-fingerprint.json)
has `custom-heap`, `default`, and `pool-adapter`, but no
`private-leaf-salts`. Its program manifest hash is
`44e411e5902369f2bf9d5759bd28d2c4ba605682d4b29fe9be05f5ef8ca1c0fe`, its
stripped ELF SHA-256 is
`76465ed0432db7cca0559b4f66092a5b5c09d74fb168d29fff7a340bf009ab99`, and
its driver SHA-256 is
`e6af6ed149d0d55cca7680cf7365d0f0c381b20f0b9b95c4d3ae3acc89f9d8f9`. It is
an adapter-only historical comparison, not the selected private-leaf-salts
configuration.

The split10 bundle preserves the five full-mask proof/public fixtures, the
13-pair lifecycle rollback checks, replay rejection, and compatibility
evidence. Those are local LiteSVM measurements; they do not establish proof
correctness, compiler refinement, or protocol security.
