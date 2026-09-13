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

`standard only` means a subset of `propext`, `Classical.choice`, and
`Quot.sound`; no retained promoted declaration reports `sorryAx` or a custom
axiom.

The standalone input prompt SHA-256 was
`ff322b7bb6060d2b34abc7ad9528c0bce637a93119db66fc4c542706570935d5`.
The archive and its referenced executable sampler certificates were absent,
so their tests are NOT RUN.
