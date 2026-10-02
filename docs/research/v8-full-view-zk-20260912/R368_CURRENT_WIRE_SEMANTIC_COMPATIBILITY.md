# R368: wire semantic compatibility

R368 adds a generic Lean reconstruction for the selected wire convention: coefficient 0 is the transmitted constant `sent[0]`, coefficient 1 is omitted from the transmitted vector and reconstructed as the incoming carry minus twice that constant and the sum of the 26 transmitted high coefficients, and those high coefficients occupy positions 2 through 27. The file proves evaluation, degree at most 27, boundary, constant/high/linear coefficient identities, and validity of the resulting round walk. It also characterizes a generic terminal guard that preserves an existing error and succeeds exactly when the actual terminal equals the claim.

`accepted_wire_compatibility` combines the generic construction with R366’s 271-coordinate model when two terminal guards succeed for the same retained result. This proves a source-shaped mathematical compatibility statement under those explicit guard-success premises.

The saved source census is `evidence/r368-wire-semantic-compatibility/source-provenance/r368-selected-semantic-degree-source-census/`. It records the frozen `semantic_cached` path, including the omitted coefficient construction and `actual != s.claim` terminal check. The census does not establish Rust-to-Lean execution correspondence.

The successful focused check was run `1790948002142284000`: exit 0, 1.55 s, peak RSS 2,055,400 KiB, swap 0. The run used systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. Its ten complete `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the two terminal-guard reports use only `propext` and `Quot.sound`. Two earlier failed drafts are retained with their exact source, logs, receipts, and `sorryAx` axiom output.

This result does not prove Rust execution correspondence, the degree of the actual terminal, or a universal C1/H1/G statement. The proof does not establish callback chronology, privacy, or security. See the [evidence bundle](evidence/r368-wire-semantic-compatibility/README.md) for source copies, run receipts, complete logs, census, and the portable verifier.
