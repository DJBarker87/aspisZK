# Replayable same-body source law

`lean/FSV8ReplayableSourceLaw.lean` instantiates the combined finite-tape
prehistory law at `ExtractionCollectorReplayableSource.replayableScript`,
including the source/OOD/gamma, middle/query/rho, and later alpha1--alpha3
continuation. The combined outcome retains the arbitrary preprogram halt and
the verifier's post-script `Returned` halt/state.

The PMF equality is proved pointwise over one uniform finite tape and lifted to
the two pushforward laws. Continuation call bounds are discharged from the
replayable script's explicit index and caller-provided total/fresh/tape budget
inequalities. No semantic-success premise, conditioning, independence, or
acceptance claim is used.

Remaining adapter: an actual adversary/source must be represented by
`preProgram` and prove those finite resource bounds. Literal Rust/Aeneas
refinement and programmed/fork K1.6 scheduler coupling remain open.

Evidence: pinned Lean 4.32.0 NUC compile, `-j1 -M8192`, exit 0, wall 3.13 s,
maximum RSS 6,582,956 KiB, swap 0. Source SHA256
`ba79b9ac618decb5bf890d4c4a4b66b5cb36fe9f26d3189b1313ca4d202b6dea`;
OLean SHA256 `81d118e2913afe060e200ec2eb1fa541214eedd01953a920b3b502d83fda01f2`.
The promoted PMF theorem reports `[propext, Classical.choice, Quot.sound]`.
