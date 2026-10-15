# Literal opening goodness and byte-run facts

This bundle records two focused Lean targets. `LiteralByteRunFacts` establishes transcript round length and the indexed round message/challenge for the literal byte-address protocol. `LiteralOpeningGood.good_of_read_noHit` transports the literal classifier's no-hit premise to the four opening exclusions, given a successful opening-data read, at least 32 entries, and explicit `gamma ≠ 0`. It does not establish those premises from acceptance, and it makes no source-correspondence or security-closure claim.

Final attempts: `LiteralByteRunFacts-c` (1.55 s, peak RSS 3,616,620 KiB, swap 0, two standard axiom reports) and `LiteralOpeningGood-b` (2.71 s, peak RSS 3,631,828 KiB, swap 0, one standard axiom report). Both used 4 GiB MemoryHigh, 6 GiB MemoryMax, swap disabled, TasksMax 128. Failed attempts are preserved: ByteRunFacts a/b and OpeningGood a. OpeningGood a's definitional-membership elaboration issue was resolved by keeping the bad-set definitions irreducible; no cap or recursion-depth increase was used.

The deterministic object archive contains the two final target objects and their direct import objects. Exact snapshots, receipts, logs, time logs, sidecars and four runner/environment pins are listed in `source-manifest.json`.
