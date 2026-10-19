# Ordinary recorded-public extractor: returned relation and conditional completeness

The existing ordinary extractor accepts only the finite recorded run and fresh private byte coins. It parses the public bytes from that run, reconstructs words from recorded commitment cuts, and invokes the maintained actual byte-GS recovery, runtime filtering, joint merge and checked witness scanner.

RawRecordedPublicSpendExtractorReturnedRelation proves that every successful output satisfies LiteralProtocol.relation for this exact run's public bytes. This theorem requires only successful output; it does not assume acceptance, terminal checks, no-hit, bank success or an externally supplied decoded public.

RawRecordedPublicSpendExtractorCompleteness proves successful extraction from terminal Checks on the actual enriched 33-row transcript, no classifier hit, and actual bank nonfailure. The successful public parse is obtained from Checks.publicParsed. The existing recorded-run bridge supplies word identity and support. Production acceptance-to-Checks and concrete transcript/source correspondence remain open.

The focused Lean 4.32 checks exited 0 in 7.68, 7.25 and 8.49 seconds, with maximum RSS 3,160,932,352, 3,160,965,120 and 3,164,405,760 bytes, zero process swaps, and only propext, Classical.choice and Quot.sound. Exact source revisions, source/object/import hashes, commands, logs and compiled objects are retained.

Earlier public-parse transport attempts normalized the large continuation/parser unnecessarily and hit the fixed 3200 MiB Lean allocation limit or recursion limit. They were not retried with a larger cap. The accepted proof factors a generic Option equality and keeps both the parser and decoder continuation opaque during elaboration. The failed attempts, including their error-state sorryAx reports, are retained as diagnostics only, not accepted proofs.

These cached focused checks are working evidence. Release evidence requires one clean ordered build on the unified research base. This packet is not a full source/runtime proof, whole-extractor polynomial-time proof, or complete 100-bit private-spend theorem.
