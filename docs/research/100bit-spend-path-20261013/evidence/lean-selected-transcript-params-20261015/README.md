# Selected transcript parameters: focused Lean evidence

This bundle records the focused green compile of `R1SelectedTranscriptParams` against source base `764bf20a6fe0392951b670f73748a54f70c9f272`. The source sets `L=131072`, `D=3717`, bounds messages by that byte length, assigns the 33 row labels and selected challenge map, and constructs a public statement only from bytes with a successful `SemanticPublicWire.parsePublic` result.

Attempt `selected-transcript-params-a` exited 0 in 1.52 s with peak RSS 3,575,132 KiB and zero swap under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. The source emits eight axiom reports; each uses only the reported standard axioms (`propext`, `Quot.sound`, and/or `Classical.choice`). The final object and three direct-import objects are archived with source and runner pins.

The bounded message subtype does not enforce row-specific message validity. This model does not establish Rust correspondence, a full protocol decision, or a security theorem.
