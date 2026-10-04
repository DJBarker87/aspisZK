# Formatter provenance

The final R687 theorem inherits `Aeneas.Std.core.fmt.Formatter` through two pre-existing results:

- `R635DecoderWholeCanonical.decoder_accepted_canonical`; its chain begins with actual packed-decoder execution.
- `R663CombineWrapperExecution.combine_beta_wrapper_execution`; its published evidence identifies the captured C1 slice / `unwrap` path.

Focused diagnostic run `1791121501143053000` printed axioms for these and for R677/R616. R635, R638, and R663 include `Formatter`; R677 chunk routing and R616 full limb execution have only `[propext, Classical.choice, Quot.sound]`.

The pinned Aeneas definition is an opaque type axiom, not a theorem assumed by R687: `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/Aeneas/Std/Core/Fmt.lean:13` contains `axiom core.fmt.Formatter : Type`. Its source SHA-256 is `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`. This provenance does not establish native adequacy of the formatter-bearing capture path.
