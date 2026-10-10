# R0 cost probe (P1 / P1′) — evidence pointers

Two Codex workers ran the probe in parallel on the same branch name; both
reports are copied here verbatim for the record. Full evidence (JSON, logs,
probe crates) lives on the pushed branches, which are never merged into
reference paths:

- `REPORT-P1-PRIME-B.md` — P1′ breakdown B on the R-E4 S4 baseline.
  Branch `codex/r0-cost-probe-p1-20261009`, commit `70544d55a`.
- `REPORT-P1-PRE-PRIME.md` — original P1, configurations C0–C4 and the C5(b)
  stop, on a baseline that includes R91 (which R-E4 found to regress by ≈7M).
  Branch `codex/r0-cost-probe-p1-pre-prime-20261010`, commit `24db293e8`.

The lead's reading of both and the decision are in
`docs/research/v8-r0-rust-20261009/PLAN.md`, section
"Lead review of P1 and P1′ … the probe closes".
