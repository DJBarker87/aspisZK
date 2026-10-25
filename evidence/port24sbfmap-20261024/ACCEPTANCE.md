# Port24SBFMAP acceptance criteria

Base: 438cd6f576b97bcf724ef523185a096205b7a18c; branch codex/cx-port24sbfmap-20261024.

1. Trace only current default f8c0ec72, devnet 63ad3e9c and Pool 121f3e29 build receipts to retained matching artifacts; distinguish receipt assertions from independently inspected metadata.
2. Pin any evidenced compiler/sysroot/allocator/Global/RawVec implementation and concrete layout association. Record absent evidence without substituting host-nightly or Kani sysroots.
3. Describe the smallest remaining implementation-identity and primitive-semantics obligations for the literal P7 path, including ordered failure prefixes. Reuse Port22 arithmetic/frame facts with explicit scope; add no equivalence premise or trust assumption.
4. Deliver source/artifact/dependency hashes and reproducible read-only investigation receipts (command, revision, exit, wall, peak RSS, swap, axioms N/A). No binary or large derived JSON committed.
5. No shipped sources, rebuilds, downloads, extraction, Kani, standalone Rust, full manifests, or other worker/candidate/cache access. Optional Lean at most seven only if an actual concrete binding lemma is supported; otherwise spend zero.
6. Commit investigation and handoff, never merge or push. Both release targets remain unestablished absent their outstanding obligations.
