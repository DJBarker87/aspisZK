# Current Wide unrolled record polynomial proof packet

This packet freezes the focused Lean proof for the seven-bind unrolled polynomial candidate. The Lean theorem is `AspisR1CurrentWide.Proof.current_unrolled_record_polynomial_success`: success of the exact ordered current-Wide port implies canonical output, seven parser-derived canonical coefficients in index order `[6,5,4,3,2,1,0]`, and the expected Horner value.

The adapter uses the actual `currentRecordFieldLookupNat` parser callback and the current Wide multiplication/addition implementations. Its theorem derives coefficient canonicality from parser success; it does not assume an arbitrary lookup-canonicality contract. The generated candidate ABI map is a nested-coordinate layout map only. Generated `WideExact.mul/add` fail/panic stubs and `weights.field` external-template axiom are excluded from the trusted proof imports.

Candidate provenance: isolated Rust source `unrolled-candidate-v1/input/lib.rs`, SHA `be90dce6ab6bc06ac357454d03ecb747313775695bcc1a60a12881db4a840eed`; function body SHA `75079706c460c8264cd5c52d07a35366d49c07167e34939e48601bfb6c9121ec`. The generated Lean candidate Funs/Types are pinned in the accompanying checker output. The candidate keeps the seven expressions ordered from index 6 down to 0.

Scope remains limited: equivalence of this explicit sequence to the original Rust `Range<usize>::rev().fold` is open; so are production adoption and full caller reachability. The Lean result establishes semantics of the unrolled current-E model and its actual parser callback, not that source rewrite's adoption.

Build record: Lean 4.32.0 SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; target exit 0 in 2.407s; process RSS 4,024,152 KiB; cgroup peak 391,340,032 bytes; swap peak 0; `#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Exact receipt, preflight, command, Lean log, and time log are under `evidence/v8/`.
