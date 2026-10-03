# R519 literal-read translation attempt V2

The corrected candidate uses the pinned Charon `Const` operand tag and preserves exactly the five captured U32 literal operands. LLBC import and FunsAnalysis completed, but translation exited 2 after 0.20 s, peak RSS 68,992 KiB, swap 0. The translator raised `Invalid_argument "option is None"` at `Aeneas.SymbolicToPure.translate_global`, `symbolic/SymbolicToPure.ml:363`, while exporting a retained literal global. No Lean files were produced.

- Candidate: `R519SharedGammaPartsLiteralReadsV2.llbc`
- Candidate SHA-256: `481629bdff71b10467071a7f5af21ef060c043efcb925888c1c8d5472aa76fb6`
- Pinned R497 binary SHA-256: `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`
- Unit: `aspis-r519-literal-global-parts-v2.service`; MemoryHigh 5G, MemoryMax 7G, swap 0, TasksMax 128; aggregate reservation checked before launch.
- Full Aeneas log, launch and receipt: `saved-output-literal-reads-v2/`.

The requested edit removed reads of Global31 and Global48 from five operands while retaining their literal-valued declaration rows. The next backend consumer still expects function-backed initializers for those declarations. No global rows or other source operations were modified, and no retry or broader normalization was attempted.
