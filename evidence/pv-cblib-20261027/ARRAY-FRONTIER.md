# Array conversion frontier

The safe reference copy loop was extracted by the pinned Charon/Aeneas pair (`op36-qm31-opt`). The generic kernel, before its QM31 wrapper, contains no foreign callback. Its mathematical shape is a length guard followed by a monotonically increasing copy index; proofs use arbitrary N and do not reduce 1,024 concrete cells.

The complete Result wrapper taking `&Vec<QM31>` failed Aeneas's fail-closed escaping-reference preflight (`aeneas-source-op36-full-opt-first-02`, exit 2, 0.10 s, 45,760 KiB, swap 0). It is rejected evidence, not a source law and not a checked counterexample. An owned-input wrapper is prepared to preserve the error input without clone. The extracted QM31 convenience wrapper still has a ZERO leaf; it must be replaced by the exact public four-limb constructor or bound to an independently extracted definition before source credit. No imported ProverRw module is edited.

The candidate native harness uses actual Vec<QM31> and Result<[QM31;1024],Vec<QM31>>. Its proposed success branch permits all four raw u32 limbs in all 1,024 entries, and arbitrary output coordinate; its rejection branch covers lengths 0–2. Until the native run and complete wrapper extraction succeed, V187 remains OPEN.

The direct-index owned Vec<QM31> variant passed Charon (`charon-source-op36-owned-opt-direct-03`: process exit 0, 0.24 s, 189,904 KiB, swap 0; has_errors=false). It contains opaque reference-returning Vec indexing declarations; Aeneas is pending. This is a changed reference, not a replay of the rejected borrowed wrapper. The copied generic Slice kernel remains accepted independently at 39661.

Aeneas rejected that direct-index owned variant for both escaping reference outputs requiring loan validation and structured Drop requiring destructor semantics (`aeneas-source-op36-owned-opt-direct2-01`). No preflight/loan/destructor validation was disabled or repaired. The complete Result adapter remains a specification, not an op36 source-binding certificate. No array native gate was run before the Kani budget was exhausted.
