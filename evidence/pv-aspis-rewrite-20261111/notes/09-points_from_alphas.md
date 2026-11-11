# `points_from_alphas` (examined, not touched)

File: `crates/aspis-core/src/r0/opening.rs`, lines 41-58.

`aspis-core` is a dependency of every program crate, and the module `r0::opening`
has no `cfg` gate. The function is called by `r0::transcript::Transcript::points`
(`transcript.rs` line 188), which is called by `r0/onchain.rs` line 80 (the
on-chain R0 verifier path, compiled for SBF), `r0/verifier.rs` line 43,
`r0/prover.rs` line 404 and `aspis-statement/src/r0.rs` lines 95 and 114. It is
therefore code that an on-chain program can reach, and it was not changed.

The translator's complaint is in the closure at lines 44-49, which captures
`carry` mutably inside `core::array::from_fn`. A counted loop over the ten
positions would remove it, but that is a change to verifier-side code and belongs
with the other verifier-side functions in a separate decision.
