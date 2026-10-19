# Rho source Option boundary: checked leaves, caller lowering open

Candidate 12 is **not complete**. No candidate-equivalence count increment.

The installed nightly-2026-06-01 standard-library bodies of Option.as_mut,
Option.map and DerefMut for &mut T are pinned in
`rho-std-source-slices.json`. `check-rho-option-source.py` verifies their exact
body transport to the extracted local generic functions: receiver lifting,
whitespace, trailing comma and runtime const declaration changes only. It
records the as_deref_mut UFCS composition but does **not** certify its nested
borrow lowering.

The original pinned producer emits the generic leaves and the exact identity
reference method. Their raw generated Lean files are promoted unchanged.
`CuSavingsRhoOptionLoans` proves their actual outcomes and writeback behavior,
including preservation of the original Option discriminant and both identity
reference handbacks. The map theorem retains arbitrary callback errors and
divergence. Packaged loan theorems retain these handbacks explicitly. They are
component theorems, not a theorem about the original consuming loop.

The original optimized library MIR is rejected on mutable-borrow copies in
DerefMut; with that primitive opaque, it is rejected in Option.as_mut. Locally
compiling the exact helper composition at built MIR instead reaches an
unsupported nested backward-type computation. A direct branch-normalized
source diagnostic also fails at nested-loan handback translation. None of
these failed emissions is accepted, and no compatible external template is
used as a source proof. Further variants of this producer experiment are not
justified by the current evidence.

`RHO-OPTION-LOANS.json` contains successful source/object/receipt pins, exact
commands and per-target axiom lists, resource metrics and failed extraction
receipts. The only proof axioms are standard propext/Quot.sound. The initial
local proof attempts failed because functional handbacks required extensional
rather than definitional equality; the corrected focused target passes.
The initial empty Types launcher was rejected before launching Lean for lack
of an axiom-audit declaration; its replacement audits id and compiles the
unchanged empty generated module. Production Rust is unchanged.

The optimized loop's original nested-borrow source binding remains open.
Independently actionable requirements are actual caller power/canonicality,
resume traversal, allocation-resource and transaction-context composition.
