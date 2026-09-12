# Combined finite-tape prehistory law

`lean/FSV8V7CombinedPrehistoryLaw.lean` defines a combined outcome retaining
the preprogram halt, then running the compiled current V8 script from the
preprogram's produced V7 oracle state. `combined_pointwise_eq` identifies this
with the current byte-level continuation using the existing exact
prehistory-continuation theorem.

`combined_current_law_eq_v7_law` lifts that pointwise equality to an exact PMF
pushforward equality over the explicit uniform finite fresh-answer tape. The
room hypotheses are supplied per tape and preserve early halt/refusal behavior;
there is no conditioning, independence premise, or acceptance claim.

The remaining adapter is explicit: an actual adversary/source must be
represented by `preProgram` and supply finite total/fresh/tape resource bounds.
This leaf does not assert that deployed ROM or an adversarial distribution has
that finite-tape law.

Evidence: pinned Lean 4.32.0 NUC compile, `-j1 -M8192`, exit 0, wall 2.86 s,
maximum RSS 6,534,172 KiB, swap 0. Source SHA256
`026b561488d84ee689efd5528b6c0e4462c692589be2105eec1f439668402841`;
OLean SHA256 `4dbbed0c4c5f6512fb4a7f4be262a45add583e236d6760d160a961960fbfc143`.
The promoted PMF theorem reports `[propext, Classical.choice, Quot.sound]`.
