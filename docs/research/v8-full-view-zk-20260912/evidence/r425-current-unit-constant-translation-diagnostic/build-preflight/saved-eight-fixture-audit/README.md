# R425 eight-check fixture saved-run audit

The checker inspects saved v1/v2 Dune build receipts and the evaluator execution receipt. It does not launch compilers, fixtures, or remote jobs. Raw phase logs and source snapshots remain at their original paths; this directory contains derived metrics, audit JSON, and report only.

The v1 failure is a source/API mismatch (`eval_operand_no_reorganize` is not exported). The v2 fixture changes to the exported `eval_operands` API, and the exact source hash is preserved. The execution log is checked for two expected `((),)` diagnostics from the pinned iterator call span and one success marker reporting eight checks. These native fixture results do not establish a Lean theorem or translator/source semantics.
