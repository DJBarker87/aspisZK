# R22 raw QM31 coefficient residue bridge

This packet contains the focused proof that the four Nat formulas for `Q::raw` coefficients, after the retained 31-bit folding operation, cast to the four coordinates of the retained QM31 `qMul` definition.

The theorem `raw_coefficients_eq_qmul` is conditional on explicit no-underflow hypotheses for each saturating Nat subtraction. It does not prove that the actual U64 machine expressions avoid wrap/underflow, nor does it prove the R22 product bounds. The source-shaped Nat formulas were cross-checked against the raw implementation separately; actual Rust `Q::raw` extraction and machine-to-Nat bridge remain open.

Accepted target: `R22RawQmProductResiduesV15`, Lean 4.32, exit 0, 1.505s, peak cgroup scope memory 252,862,464 bytes, swap peak 0. Axiom reports are in the receipt/log; theorem reports use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

V8–V14 failed attempts are preserved under `failed/` with their receipts and logs. V9 additionally contains an import-root typo caused by a namespace rename; V8 failed at premature expansion of P²; later versions progressively exposed/fixed nested cast rewrites. These attempts produced no accepted objects.

No `.olean`, `.ilean`, `.ir`, generated binary, or production source is included. The full NUC config and exact direct import pins are under `evidence/v15/`.
