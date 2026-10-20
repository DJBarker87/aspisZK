# Blocked composition — unaccepted sources

These `.lean.txt` files are retained proof attempts and dependent drafts. They
are not accepted Lean modules, a certified costed extractor, or a final
soundness endpoint. Do not import or treat them as established theorems.

The isolated continuation definition compiles. The isolated value proof and
isolated work-bound proof fail at the unchanged local `-M4400` kernel limit.
Both generic stage composition and generic equality-transport lemmas compile;
the failures occur when specializing the proof to the actual GS/point/private
tape expressions. The work-bound attempt contains no required value theorem,
so the cost aggregation failure is independently isolated.

Focused obstruction receipts:

- `../ActualContinuationValueM10-1/receipt.json`: kernel excessive memory,
  37.041 s, 4613783552 bytes peak RSS, zero swap.
- `../ActualContinuationValueM10-3/receipt.json`: changed proof uses generic
  equality transport and explicit source unfolding; signal 6, 10.915 s,
  4790272000 bytes peak RSS, zero swap.
- `../ActualContinuationBoundM10-1/receipt.json`: isolated generic work-bound
  specialization, kernel excessive memory, 13.680 s, 4772626432 bytes peak RSS,
  zero swap.
- `../ActualExtractorWorkM10-5/receipt.json`: separated value premise and
  resource proof; work theorem still fails in the kernel, 56.964 s,
  5428576256 bytes peak RSS, zero swap. The other type error is preserved.

The complete Resources instantiation and R19 endpoint drafts were not compiled.
The generic quartic reservation and fixed-family coordinate/degree lemmas are
accepted component results, not an implementation ledger. No release replay
was launched because the required focused bridge is not green.

A lead decision is needed on an alternate composition/proof interface or build
route. Existing Lean modules were left unchanged. An unchanged larger-cap
retry is forbidden by AGENTS.md; local-lean.txt also fixes the local compiler
flags and prohibits changes to existing modules. No cap or recursion/heartbeat
limit was increased. All source hashes are in `sources.json`, and each failed
attempt has its own exact source snapshot, command, imports, timing and log.
