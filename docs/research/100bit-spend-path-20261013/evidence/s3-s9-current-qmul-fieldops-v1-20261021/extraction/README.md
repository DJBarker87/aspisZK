# Current `WideExact::mul_qm31` extraction receipt

This snapshot is the accepted nonempty NUC Charon/Aeneas extraction of the frozen `field/wide_exact.rs` method and its free wrapper. The raw generated `Funs.lean` is retained for provenance only; it contains generated resource `set_option` declarations and is not imported into the option-clean Lean proof closure. `check-generated-qm31.py` checks the four copied declaration bodies in `S3S9GeneratedWideMulQM31V2.lean` against the raw generated snapshot after whitespace and documentation-comment normalization.

The Lean adapter still has a separate typed coordinate-map proof obligation. The generated result establishes the method body from the pinned source; it does not establish the enclosing `Weights::pair` call path or claim production adoption.
