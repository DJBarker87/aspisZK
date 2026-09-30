# R140 nonzero source/model report

The actual R137 three-attempt nonzero sampler now matches the existing
source-shaped `nonzeroRun` model in result and advanced state.  The proof uses
the exact R139 QM31 sampler bridge and the generated QM31 equality code; no
hiding or distribution assumption was added.

Focused result: exit 0, wall 2.20 seconds, peak RSS 3,711,056 KiB, swap 0.
Printed axioms are only `propext`, `Classical.choice`, `Quot.sound`, plus the
already-extracted `core.fmt.Formatter` axiom in the slice conversion path.

Callback execution, q22 source binding, admissibility, privacy and soundness
remain open.
