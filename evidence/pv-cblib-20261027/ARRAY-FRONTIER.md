# Array conversion frontier

The safe reference copy loop was extracted by the pinned Charon/Aeneas pair (`op36-qm31-opt`). The generic kernel, before its QM31 wrapper, contains no foreign callback. Its mathematical shape is a length guard followed by a monotonically increasing copy index; proofs use arbitrary N and do not reduce 1,024 concrete cells.

The complete Result wrapper taking `&Vec<QM31>` failed Aeneas's fail-closed escaping-reference preflight (`aeneas-source-op36-full-opt-first-02`, exit 2, 0.10 s, 45,760 KiB, swap 0). It is rejected evidence, not a source law and not a checked counterexample. An owned-input wrapper is prepared to preserve the error input without clone. The extracted QM31 convenience wrapper still has a ZERO leaf; it must be replaced by the exact public four-limb constructor or bound to an independently extracted definition before source credit. No imported ProverRw module is edited.

The candidate native harness uses actual Vec<QM31> and Result<[QM31;1024],Vec<QM31>>. Its proposed success branch permits all four raw u32 limbs in all 1,024 entries, and arbitrary output coordinate; its rejection branch covers lengths 0–2. Until the native run and complete wrapper extraction succeed, V187 remains OPEN.
