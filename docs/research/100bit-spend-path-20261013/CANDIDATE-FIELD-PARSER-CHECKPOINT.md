# Candidate field-parser checkpoint

The original candidate-parser batch has seven green Lean targets: [`ParserArraySlice`](lean/ParserArraySlice.lean), [`CandidateFieldParsers`](lean/CandidateFieldParsers.lean), [`CandidateParserSupport`](lean/CandidateParserSupport.lean), [`CandidateCM31Parser`](lean/CandidateCM31Parser.lean), [`CandidateQM31Parser`](lean/CandidateQM31Parser.lean), [`CandidateFieldCanonicality`](lean/CandidateFieldCanonicality.lean), and [`CandidateParserCheckpoint`](lean/CandidateParserCheckpoint.lean). The nine recorded attempts include two failures and seven final successes. Their 38 axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`; receipts, snapshots, logs, source pins, and objects are in [`lean-candidate-field-parsers-20261014`](evidence/lean-candidate-field-parsers-20261014/). The original M31 proof is recorded at source commit `6e25cda9` in [`lean-m31-parser-20261014`](evidence/lean-m31-parser-20261014/). A separate extension adds three further green targets: [`CandidateParserByteOrder`](lean/CandidateParserByteOrder.lean), [`CandidateStrictQM31Parser`](lean/CandidateStrictQM31Parser.lean), and [`CandidateStrictParserCheckpoint`](lean/CandidateStrictParserCheckpoint.lean). The extension preserves six attempts (three failures, three final successes) and 18 successful axiom reports in [`lean-candidate-strict-parser-20261014`](evidence/lean-candidate-strict-parser-20261014/).

The retained generated module is checked against pinned Aeneas `Types.lean`, `Funs.lean`, translation metadata, and LLBC Option tags by [`check-candidate-field-parsers.py`](tools/check-candidate-field-parsers.py). Its parser bodies retain the generated M31, CM31, and QM31 definitions and the source-bound R259 Option discriminant support. The only candidate source change is in CM31: its two `try_into().ok()?` conversions use explicit `Ok`/`Err` matches that return `None` on conversion failure. The M31 and QM31 bodies are unchanged. The Lean bridge reuses the retained M31 byte decoder and value conversion, the checked slice conversion lemma from `SamplerWordRead`, and the R259 Option-tag support; it then proves refinement for every fixed 8-byte CM31 array and every fixed 16-byte QM31 array. Successful decodes imply each returned limb is below the M31 modulus, with no canonical-input premise.

The pinned optimized Rust differential harness compares the complete baseline and candidate field modules, including both `wide_exact.rs` siblings. It passed 221,597 deterministic byte vectors and 443,194 CM31/QM31 parser comparisons, classifying outcomes as panic, `None`, or decoded limbs. The run record and inputs are in [`parser-candidate-differential-20261014`](evidence/parser-candidate-differential-20261014/). This is finite differential evidence.

The extension checks the fixed-array `Fin 16 → Byte` byte-order bridge and the strict decoder bridge to four canonical `Fin P` limbs returned by `decodeQM31LE`. These results are in the three extension targets linked above. Caller-level work still needs to show which checked record payload reaches each parser at the required width: these Lean refinements use fixed arrays, while the Rust parser APIs accept slices. The runtime `WideExact` parser consumes 32 bytes and eight limbs, and its encoding and any QM31-subfield condition still need a separate connection. Compiler/translator trust and the full protocol-security argument also remain outside these parser theorems.

The exact two-call rewrite is now applied on the research branch. The
[corrected build](evidence/parser-candidate-v152-sbf-20261014/) pins Solana
`cargo-build-sbf` 3.1.13 (SHA-256
`46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c`),
platform-tools v1.52, and rustc 1.89.0. Its 751-file source manifest differs
from the baseline only in `field.rs`, which hashes to
`28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`.
The build completed in 46.043 seconds under a 4 GiB high / 6 GiB maximum /
zero-swap scope. The [passing local-SVM gate](evidence/parser-candidate-v152-cost-20261014/)
reused the exact proof generated with full OS masks during the initial run,
including its public statement. Verification and settlement passed:

| Artifact, same proof/public | First transaction CU / bytes | Terminal transaction CU / bytes |
|---|---:|---:|
| Historical P3, platform-tools v1.52 | 1,390,128 / 295 | 1,293,571 / 879 |
| Applied parser rewrite, platform-tools v1.52 | 1,390,128 / 295 | 1,293,571 / 879 |

Both transaction limits were 1,400,000 CU. The measured headroom is 9,872 CU
and 106,429 CU. All expected settlement flags passed. This is one exact-proof
comparison, not a bound over every possible mask value.

The [ELF comparison](evidence/parser-candidate-v152-sbf-20261014/elf-versus-historical.json)
finds identical executable `.text`, `.rodata`, relocation, and other sections;
only eight bytes in five `.data.rel.ro` line-number words differ by +8,
matching source lines shifted by the rewrite. The selected new ELF hash is
`fca47fb42d1123116ba34b0da5a2af05af0897cfb0f92224ec01885aac56bea8`.
The changed byte values and locations are recorded explicitly; this is a
mechanical comparison, not a theorem about arbitrary SBF execution.

The first builds accidentally selected the older installed Solana 2.3.0 /
platform-tools v1.48 / rustc 1.84 toolchain. Both candidate and unchanged-source
control exceeded the first transaction's budget on the same proof. Their
code sections and failure logs were identical. The historical artifact then
passed that proof. The [fingerprint comparison](evidence/parser-build-fingerprint-comparison-20261014/)
identified the toolchain difference, and rebuilding with v1.52 restored the
historical cost. The failed candidate/control receipts remain in
[`parser-candidate-cost-20261014`](evidence/parser-candidate-cost-20261014/)
and [`parser-control-cost-20261014`](evidence/parser-control-cost-20261014/);
the separate historical replay is in
[`parser-historical-reuse-cost-20261014`](evidence/parser-historical-reuse-cost-20261014/).

This checkpoint establishes parser-model refinement, finite differential results, and the measured two-transaction cost of the applied rewrite. Caller widths/composition, the `WideExact` parser bridge, compiler/translator correctness, full privacy, and the concrete adaptive Fiat–Shamir security instantiation remain open. It does not establish a 100-bit private-spend security theorem.
