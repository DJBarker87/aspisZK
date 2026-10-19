# Executable byte frames and finite recorded-log word recovery

RawTranscriptFrameBytes defines ordinary computable byte constructors for public initialization, absorption, the dedicated row-zero record, advance, and opening reseed. Their compatibility equalities identify the exact bytes of the retained semantic frame constructors. No field challenge decoder or specification extractor is evaluated by these definitions.

RawCutRecordedWordsExecutable computes first-occurrence cut positions by structural recursion, takes the chronological prefix before each supplied frame, parses finite tagged Merkle records, recovers paths, and applies the existing typed zero-default word projections. Its result equals wordsFromRawCuts, including the same three root parsers at indices 8, 8 and 9. The compatibility theorems have no assumption that separately supplied recovered words are already equal. Frame byte strings are still supplied to this component.

Both smallest changed modules passed focused Lean 4.32 checks. The byte module exited 0 in 17.64 seconds with peak RSS 3,017,605,120 bytes; the word module exited 0 in 9.46 seconds with peak RSS 3,070,001,152 bytes. Both report zero process swaps and only standard axioms. Raw commands, source revisions, exact source/object/import hashes and complete axiom output are retained. These are focused checks; no full manifest replay or production-source change occurred.

The remaining executable-caller obligation is proving state-only replay through row 30 selects the same actual commitment frames at rows 0, 2 and 30, then composing these primitives with the fixed-word extractor. Accepted-source validity and opening/semantic checks remain separate obligations; this packet does not establish complete 100-bit soundness or runtime correctness.
