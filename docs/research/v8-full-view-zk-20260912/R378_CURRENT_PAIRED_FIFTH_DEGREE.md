# R378: paired fifth-power degree fragment

R378 proves a degree bound for a declared exact-field polynomial model. A linear layer preserves the common degree bound of its input coordinates. One fifth-power round maps input and constant coordinate bounds of 1 to a bound of 5; two paired fifth-power rounds therefore have degree at most 25 in the univariate variable. The theorem `leading_pair_degree` also bounds the declared absorbed state by 1 using the ordinary and xor model claims, then carries that bound through a declared linear layer and the two fifth-power rounds.

The promoted target is [R378PairedFifthDegree.lean](lean/AspisV8R19/R378PairedFifthDegree.lean). Its only focused run exited 0 in 2.37 seconds, with 2,619,584 KiB peak Lean-child RSS and no swap. All five complete `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The target imports the saved R376 simple-point degree result, which in turn depends on R374's source-point polynomial fragment; their exact source hashes are included in the evidence bundle.

A short excerpt from the selected frozen Rust source records the `pow5` helper and calls used by leading and interpolated full-round pairs. It is included only as provenance. In R378 the field matrices and constants are arbitrary declared data, and the theorem does not show that those declarations implement the selected Rust linear packing, constant handling, or fifth-power execution.

The first remaining source obligation is to show that the selected leading and interpolated full-round field execution equals the declared matrices, constants, and packing in this model, including word reductions and error behavior. The saved pow5 excerpt alone does not discharge that correspondence.

This result is not an actual Rust execution refinement, a degree bound for the complete selected terminal, or a source error/stopping correspondence. It does not establish correction existence, universal mask coverage, a simulator, or security.
