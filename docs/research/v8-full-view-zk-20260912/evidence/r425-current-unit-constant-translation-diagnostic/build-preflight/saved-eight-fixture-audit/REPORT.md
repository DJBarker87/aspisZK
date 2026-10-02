# R425 eight-check fixture evidence audit

PASS — Saved R425 8-check fixture build and execution evidence only; no reruns. The checks are finite native behavior on exact R419 LLBC and do not prove translator or Lean/source correspondence.

The first build attempt failed to compile because the fixture named private `eval_operand_no_reorganize`; the saved compiler diagnostic says it was unbound. The corrected source uses exported `eval_operands` and built successfully in 1.48 s with 296544 KiB peak RSS and zero swaps. Its execution passed eight checks in 0.13 s with 49808 KiB peak RSS and zero swaps. The raw output contains the expected unsupported `((),)` constant diagnostic twice at `iterator.rs:2486:4-2490:35`, followed by the single eight-check success marker. Systemd and Docker receipts confirm the capped scope. No Lean theorem or source-execution correspondence was proved.
