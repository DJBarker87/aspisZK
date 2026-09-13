# Fresh-cut focused Lean evidence

Host: `nuc` via Tailscale (`100.108.41.90`)

Toolchain: Lean 4.32.0

Resource scope: `MemoryHigh=7500M`, `MemoryMax=8G`, `MemorySwapMax=0`

| Source SHA-256 | Target | Exit | Wall | Maximum RSS | Swap | Axioms |
|---|---|---:|---:|---:|---:|---|
| `28a983223b63bef00676243919eeb10897078c56bad55ac9aa82ef3d4f680107` | `FSV8ProgrammedAlphaMarkerHistoryPrefix` | 0 | 8.70 s | 6,797,084 KiB | 0 | standard only |
| `134c130a7c74864be2105b344d955be6a5654177c1594be9719fd4680ace58b1` | `FSV8OutsideTargetTraceClean` | 0 | 2.74 s | 6,803,860 KiB | 0 | standard only |
| `c4cf0faaf17735032f5edf7f6f4df53a723bec51994431d8b2e95b05a6286b01` | `FSV8MarkerFreshVerifierQueryBridge` | 0 | 2.70 s | 6,809,744 KiB | 0 | standard only |
| `c02ee311edf500e118a9c50ac897e0daf26db69d84f1762fd2d9fa8e7e245e26` | `FSV8MarkerFreshVerifierMembership` | 0 | 4.11 s | 6,832,392 KiB | 0 | standard only |
| `b214792568bbe3d6ba69335298372aad48d5077f7fbe06395c07b72d3a25bcd0` | `FSV8FreshRequestTargetEvent` | 0 | 2.81 s | 6,795,844 KiB | 0 | standard only |
| `acc2d09877157c585edd344b5ad936b660bf90bd3cca29be6721c1cd71ac35d9` | `FSV8ReturnedRootFreshTracePrefix` | 0 | 2.69 s | 6,765,448 KiB | 0 | standard only |
| `4d1a0360e6cf1b2b63d6e438b7eba691c3f56a71a6d219e662f9de267e81a5dc` | `FSV8RootVerifierNativeRequest` | 0 | 2.82 s | 6,828,692 KiB | 0 | standard only |
| `be4095808c2e5ec033138a948158ec81961d8ac11fd963fae5a970c63becb842` | `FSV8ReturnedVerifierFreshTargetEvent` | 0 | 2.84 s | 6,827,416 KiB | 0 | standard only |
| `66752f7c33f0b1c7c7fdbc09f2f3466e0a09c7eafce320518ac9904264626bd2` | `FSV8MarkerFreshEnumerationSplit` | 0 | 2.79 s | 6,806,952 KiB | 0 | standard only |
| `c8cbe92185b973f3d2aec29bacbd7833e367500699b08db5cfeeeb187baa2f2c` | `FSV8MarkerFreshCreatorTargetEvent` | 0 | 2.85 s | 6,831,952 KiB | 0 | standard only |
| `01153916b82896d74d184c15d95c75e69dd30731ff8cae26336e25789ca6c352` | `FSV8MarkerFreshTargetReduction` | 0 | 2.88 s | 6,828,428 KiB | 0 | standard only |
| `a72d4cd28175f01a9d654b9ec975673fafc405479d397411f9ede25b4688977c` | `FSV8OperationalTargetMonotone` | 0 | 2.64 s | 6,789,056 KiB | 0 | standard only |

Subsequent focused checks also passed for the following exact sources.  Their
source hashes and exit status are retained here; final release evidence must
add the lead runner's captured wall/RSS receipts rather than reconstructing
resource figures from systemd timestamps:

| Source SHA-256 | Target | Exit | Wall | Maximum RSS | Swap | Axioms |
|---|---|---:|---:|---:|---:|---|
| `d5560254e62a606bf622ce39e7b3be6263674c87562ce450997c2d64bcc3044c` | `FSV8MarkerFreshVerifierCut` | 0 | 6.08 s | 6,829,892 KiB | 0 | standard only |
| `4b4777917c8352d826cf981081378de03c82f6ce923c94670f6a1673edde1b66` | `FSV8PreAlphaMarkerCreator` | 0 | 3.31 s | 6,806,324 KiB | 0 | standard only |
| `a3caf2b3c5a93cd50ee2f166b7f8e16b596fca2a9e1b8c1085c865f475fa8d6d` | `FSV8AcceptedExactRootAlphaMarkerTargetEvent` | 0 | 19.11 s | 6,868,896 KiB | 0 | standard only |
| `6daf578881e080a80fadc477462849b4268787ecd93dc96f3986c95c281bf3e4` | `FSV8AlignedAlphaInitialPairDisposition` | 0 | 2.63 s | 6,793,076 KiB | 0 | standard only |
| `0f461499c6ca5f040199ba6ef8c743d6cb418a67005cc4bf4afd495c3d9641e8` | `FSV8AlphaTotalSuccessfulCoordinates` | 0 | 2.78 s | 6,821,508 KiB | 0 | standard only |

The accepted marker theorem constructs a source-level four-way classifier:
prior adversary, fresh marker already charged to the exact-root target event,
cached marker retained explicitly, or candidate absent at the candidate cut.
The aligned-pair theorem constructs the common-initial-state split for one
actual output/advance pair.  Neither proves the complete four-pair ordinary
sampler law, a cached first-exposure charge, or the fixed-alpha distribution
for the actual V8 source execution.

`standard only` means a subset of `propext`, `Classical.choice`, and
`Quot.sound`; no retained promoted declaration reports `sorryAx` or a custom
axiom.

The standalone input prompt SHA-256 was
`ff322b7bb6060d2b34abc7ad9528c0bce637a93119db66fc4c542706570935d5`.
The subsequently downloaded fresh-cut archive SHA-256 was
`32b8694bc734d68df471499e8d50f3ef6dcacd90bba94e3e2d27a1b3b07379c5`;
all entries passed its supplied `SHA256SUMS`.  Intake reran the supplied 61
Python tests (exit 0, 0.29 s wrapper wall, 26,918,912-byte maximum RSS) and
certificate generator (exit 0, 0.08 s wrapper wall, 23,101,440-byte maximum
RSS).  These are reference-model checks, not Lean/Rust/source-law evidence.
