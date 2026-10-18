# Executable splitting backend and bounded retries

These focused results connect the existing Cantor–Zassenhaus probability lemmas to executable polynomial operations. They do not establish a complete efficient extractor or the full spend soundness theorem.

- `CompPolyPolynomialBackendBridge` implements binary modular exponentiation using the pinned CompPoly polynomial representation. Its gcd and modular-power results agree with the existing mathematical specification. Two small ZMod 7 evaluations exercise the actual implementations.
- `CompPolySplitTrial` executes both normalized gcd tests, with no field enumeration or dense X^q construction. The actual result is successful exactly when the proved mathematical trial is successful. Under the stated monicity, odd-field and two-distinct-root hypotheses, its uniform linear-probe failure probability is at most one half.
- `CompPolySplitRetries` executes at most t independent probes and returns none on exhaustion. Its actual failure indicator equals the finite product of trial indicators; its failure probability is at most 2^-t. Separate adaptive recursion nodes still need independent tapes and a global failure bound.
- `CompPolyScaleRowCost` instruments one actual dense-kernel row-scaling loop. Its data projection equals the library loop and its counter equals the number of columns. This is a first operation-count component, not an aggregate extractor runtime theorem.

## Reused dependency

CompPoly is pinned to `4165a87dd9a9ede48ee4dc5b4fe825604b8bb932` (tag `4.32.0-cache`), with mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, matching this campaign's Lean 4.32 toolchain. The matching release object archive has SHA256 `3bd45d463d42135bbc2cdbfa121bd389720e94a42326976aec22e6bd51a44897` and is obtained from https://github.com/Verified-zkEVM/CompPoly/releases/download/4.32.0-cache/CompPoly-oleans.tar.gz . The archive is not included here; no project toolchain upgrade or cold dependency build occurred. Direct source/object pins appear in each receipt. For custom imports whose original receipt has no source path, the accepted producer's object SHA in this manifest identifies the dependency.

## Verification and limits

Each receipt records exact target, exit status, wall time, process RSS, process swap count, source revision, direct imports and axiom reports. All four accepted checks exited zero with only standard axioms; process swap counts were zero, while pre-existing host swap usage is explicitly recorded and was not zero. The controller capped aggregate local Lean RSS at 4 GiB and used -M2048. Existing compiled caches were reused; no full regression was repeated.

Still open: returned-factor recursive decomposition and root completeness, independent randomness at adaptive nodes, concrete sampler correspondence, aggregate operation/bit costs, actual GS/RR integration and final candidate bounds. No production source, deployed artifact or security parameter changed in this packet. This packet must not be described as 100-bit soundness completion.
