# Source-shaped byte sampler rank model

This bundle records `AspisR1.SourceSamplerByteRank` and its focused proof that a fixed 32-byte Aeneas array's decoded eight words have the same positional value as the corresponding `R0C.ModuloField.blockRank`. It then composes the existing repeated `machineProcess`/Nat low-digit model for the 4-pass QM31 digits, 8-pass ordinary digits and quotient, and end-around gamma digit value.

Attempt a is retained as a failed predecessor. Attempt b is the final green compile: exit 0, 1.67 s, peak RSS 3,807,660 KiB, swap 0, under the 4G/6G/0/128 cap. Its seven axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem input is an already-decoded fixed-width byte array. This composition does not establish that the Rust sampler loop's reads, retry branches, repeated state updates, or returned value refine the model.

Failed-attempt axiom reports are counted as emitted provenance. They are not counted as successful-target audits; only exit-0 final attempts support the successful audit summary. Attempt a emitted seven reports, including two containing `sorryAx` (`gammaBytes_eq_gammaDigits` and `gammaBytes_value`), and remains failed.
