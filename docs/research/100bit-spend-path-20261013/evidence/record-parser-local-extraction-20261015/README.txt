Exact-source row_shape and parse_record extraction evidence.

See design/J1-B-RECORD-PARSER-EXTRACTION-20261015.txt for outcomes,
source boundaries, and remaining obligations. row-shape-a and parser-e
contain the final generated declarations; parser-d retained one opaque
Option::ok_or dependency resolved by parser-e. Both original parser failures
remain unchanged. The actual runtime helper refactor and two passing
optimized regression tests are retained with before/after source.

Reusable runner: tools/record-parser-extraction-kit/run-local.py; parser
requires --target parse-record --include-option-methods --output FRESH_PATH.
Each attempt preserves exact commands, sources, tool hashes, LLBC, logs,
and resource receipts. No generated Lean compile or refinement is claimed.
