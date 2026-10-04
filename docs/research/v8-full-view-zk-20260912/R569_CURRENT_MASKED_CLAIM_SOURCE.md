# R569 current masked-claim source extraction

The selected Rust function `begin_state_only_masked_sumcheck` and its captured dependencies now have a focused, compiled Aeneas/Lean extraction. This is a source-extraction milestone only. It does not prove claim-address injectivity, execution correspondence, privacy, or security.

The capture uses frozen selected-source revision `6677d5f1310ff7373301fbd79f186278f772e68a`. The campaign repository HEAD recorded at capture was `95261201338bfba305516455f07bfb55d014f17d`. The selected `aspis-core` files are byte-identical to the freeze. The isolated Charon stage added only a host-side `claim_probe` wrapper around the selected function; that wrapper is not part of the selected verifier. The two captured source constants, including the schedule constants, are the compiler-captured initializers and values, not hand-written templates.

The target-only Charon capture had no LLBC errors and preserved the generic `Option` structure. The Aeneas translation emitted structured generated bodies for the actual begin function, its `From<ChallengeSampleExhausted>` conversion, transcript absorb and challenge functions, QM31/CM31/M31 byte writers, and the selected source constants. The generated `Types.lean` and `Funs.lean` then compiled with Lean 4.32.0. The sole adaptation replaced the unavailable aggregate import `Aeneas` by three already-cached leaf imports; no generated declarations or bodies changed.

The full 38-declaration `#print axioms` audit is saved in the evidence folder. The actual begin function and challenge/nonzero samplers include the opaque standard-library type axiom `Aeneas.Std.core.fmt.Formatter`, alongside `propext`, `Classical.choice`, and `Quot.sound`. Its exact pinned definition is in the saved `Aeneas/Std/Core/Fmt.lean`, SHA-256 `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`; line 13 declares `axiom core.fmt.Formatter : Type`. The field byte writers and transcript absorb use only the foundational Lean axioms listed by the audit. The `map_err` and conversion functions report no axioms.

The next required proof is to bind this actual function's record writes and sampler execution to the selected transcript chronology, including failures, stopping behavior, and shared-oracle behavior. That execution result must then feed the claim-address and adaptive-view arguments. No end-to-end privacy or security claim follows from this extraction.

Evidence and exact source/tool/input hashes are in [r569-masked-claim-execution](evidence/r569-masked-claim-execution/RESULT.md).
