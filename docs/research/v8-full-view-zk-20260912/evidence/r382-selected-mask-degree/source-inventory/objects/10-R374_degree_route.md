# Lead degree route: selected terminal

Status: proof route only; no degree or source-execution obligation closed.

Pinned selected state_only_poseidon.rs SHA 4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe. Lines 350-411 and 481-541 call pow5 in two composed rounds. The earlier informal pow7 estimate in resume reasoning was incorrect for this selected source. The correct paired degree bound is 25, not 49 or 7.

First prove univariate source statement point coordinates affine when exactly one original coordinate varies. The successor carry product contains that variable at most once; if the coordinate itself varies, its successor carry excludes it. Do not assume a successor-point multilinear opening is affine: it has degree at most 10 after ten factors.

Ordinary/xor multilinear openings can be bounded by 1; successor by 10. For selected Poseidon two fifth-power rounds, input and interpolated constants have degree at most 1, hence degree at most 25. Local selectors use the last four coordinates, block selector the first six. Their per-variable degree contributions sum to at most 1, and equality adds at most 1, giving 27. Do not independently add 1 for both selector factors in the same variable.

Range successors squared have degree at most 20, selectors add at most 1, equality at most 1, giving 22. Positive transfer residual claims[1]*claims[29]*claims[3]-1 has degree at most 12, selector/equality at most 1 each, giving 14. Ordinary C1/mask-only/G openings have degree at most 1; selected linear factors to exponent 26 give at most 27. Copy and all semantic helper expressions must be represented and bounded from their exact selected source; no placeholder degree premise for them.

The intended final argument also needs honest source enumeration/28-node interpolation correspondence and source errors/stopping/transcript behavior. A polynomial expression bound alone is not that correspondence, universal mask coverage, or a simulator.

## Read-only selector coordinate census

The saved R117 source maps the selector split as follows: `Selectors::at_point` passes the first six point coordinates (`point[..6]`, indices 0–5) into `high`, and the last four (`point[6..]`, indices 6–9) into `low`; `poseidon_selectors` uses `sum_high(selectors, &[0..57])` for `block` and copies `selectors.low` into `local`. The range is half-open, so the block sum reads high entries 0–56. The projected Poseidon evaluator uses `local[0]`, the sum of local entries 1, 9, 10, the sum of entries 2–8, and passes `local` to full/internal interpolation helpers; it separately prepares `block`. The terminal calls `Selectors::boxed_at_point(point)` before projecting and evaluating. Exact paths, line spans, complete-file hashes, and the source-only limitation are recorded in `.r21-scratch/r374-selector-split-census/census.md`. This is a source-coordinate inventory only; it does not establish a polynomial degree bound.
