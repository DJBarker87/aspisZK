# Batched audit completed

14 successful query-file attempts (578–591), groups of at most 100 modules,
cover all 1378 green contexts. 60248 structured declaration
queries and 60248 raw printed results. No missing audit
module, header mismatch, duplicate owner/name query or completion error.
The standard-only gate for ALL declarations is false: 72 formatter records
use 37 nonstandard axioms. Two equality definitions share axiom-free formatter
matchers; RPz3_FORMATTERS.md names them. No whole-top reachability claim.

Budget to this stage: 591/1500 Lean, 0/0 Kani. All 14 audits passed; source
attempts: 576 passed, one raw serializer failure retained and corrected by a
changed committed source. Peak RSS 4625476 KiB, swap zero.
Compiler wall sum 2093.088474536722 seconds. Final consistency check next.
