# Literal semantic-prefix reader evidence

This focused Lean target defines a strict reader for the selected semantic prefix of the literal transcript model. Its C2 message supplies the callback used when a semantic record decodes as a C2 root; the reader is modeled only for ordinary challenges and offsets below 25. The two audited results are `read_length` and `read_append`.

The pinned NUC run compiled `R1LiteralSemanticPrefix` attempt `a` successfully under Lean 4.32.0, `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`. It took 2.21 seconds, peaked at 3,592,028 KiB RSS, and used no swap. The output contains two benign unused-simp-argument warnings and two `#print axioms` reports, each listing `[propext, Classical.choice, Quot.sound]`.

This is a mathematical transcript-reader model. It does not establish Rust source correspondence, verifier acceptance, a causal word-recovery theorem, or a probability bound.
