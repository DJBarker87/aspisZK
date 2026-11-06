# Exact failing and retired steps

- K001/K002: source transport omitted frozen optional z4 and cert-build/check manifests; fixed by importing exact Git inputs, no Kani proof ran.
- K003: package-specific cargo-kani rejects another package's qualified features; corrected to the statement crate's deployed `pool-v1-kernel` and recorded exact dependency features.
- K004/K005: missing frozen cfg(kani) reference inputs and incorrect own Rust module path; fixed, no proof passed.
- L001: missing nested output directory in own client; fixed before L002, no host tooling changed.
- L006: audit objects not part of the combined theorem closure; copied exact retained walker/fixtures, pinned, L007 succeeded.
- K008/K014: generic From trait contracts not supported by pinned Kani. Direct observations K019–K024 cover all16/24/13 cases with passing positives and failing inverses, but are NOT the mandated proof_for_contract and do not close159/160/189.
- K025: 8KiB arbitrary RootHistoryPage construction led to90s solver timeout; K026 not launched. Do not retry the full-page shape, including its inverted form.
- L018: own proof used `.proper` instead of the actual Subtype `.property`; failed draft emitted sorryAx through Lean's error recovery and is EXCLUDED. L019 repairs it and prints only standard axioms.
- E004: full frozen Pool reference extraction timed out during dependency compilation at180s. No replay of that selection. E005 isolates only the two-record vault projection in a dependency-free reference crate; it passes. Field-for-field/type/source correspondence is recorded separately; no full-Pool extraction is claimed.
