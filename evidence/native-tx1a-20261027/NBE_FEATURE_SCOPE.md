# NBE feature scope

Kani checks the cost-probe library with its manifest defaults and explicit
harness-only cfg(kani), optimized dev profile. It does not build the Solana
release feature set or ELF. The selected multiproof/key/leaf/offset source
bodies contain no feature-selected arithmetic branch; their source pins are
unchanged across the frozen releases. Native field evaluation, Prepared layout,
release dispatch and target ABI are not proved by these helper gates.

Default/devnet frozen verifier release commands use pool-adapter and
private-leaf-salts, with optimized-terminal expansion. No host harness result
is a whole release configuration or source-to-ELF proof. Actual source-only
freeze validation and full tool/command/dependency receipts are retained.
