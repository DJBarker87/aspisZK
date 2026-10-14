# Terminal oracle composition evidence

This bundle records focused Lean evidence for the terminal oracle-reading verifier wrapper, trace decomposition and append transport, the total decoder case for terminal reads, and its composition into the `Inj3` interface. The decision program is arbitrary; the only query-size premise in the injection interface is the explicit whole-experiment bound on distinct first reads.

The final checkpoint imports the terminal verifier, trace append facts, follow append facts, trace decomposition, total decoder case, and the `Inj3` adapter. It prints 13 public axiom reports. Evidence includes seven green targets and every available failed attempt snapshot. The pinned NUC checkpoint ran with `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`; exact receipts, source snapshots, runner pins, and object hashes are recorded in `source-manifest.json`.

This bundle establishes only the archived Lean statements under their premises. It does not provide a numerical security bound, an efficient extractor, or closure of the D1/D2/D3 obligations.

The historical failed `R1UnifiedOracleVerifier-a` source is retained separately from the compiled unprefixed `UnifiedOracleVerifier` module. In the pinned workspace, unprefixed `UnifiedOracleVerifier` attempts `b` and `c` are present; no unprefixed `a` receipt/source was found.
