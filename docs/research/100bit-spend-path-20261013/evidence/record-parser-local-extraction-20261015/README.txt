Exact-source row_shape and parse_record extraction evidence.

See design/J1-B-RECORD-PARSER-EXTRACTION-20261015.txt for outcomes,
source boundaries, and remaining obligations. row-shape-a and parser-f
contain the latest generated declarations; parser-e remains the pre-header
version whose target audit found a Formatter dependency. parser-d retained one opaque
Option::ok_or dependency resolved by parser-e. Both original parser failures
remain unchanged. Header attempt F removes the target unwrap after the same
length/tag guards, preserving all derives; see J1-B-HEADER-ARRAY-20261015.txt.
The actual runtime helper refactor and two passing
optimized regression tests are retained with before/after source.

Reusable runner: tools/record-parser-extraction-kit/run-local.py; parser
requires --target parse-record --include-option-methods --output FRESH_PATH.
Each attempt preserves exact commands, sources, tool hashes, LLBC, logs,
and resource receipts. No generated Lean compile or refinement is claimed.
