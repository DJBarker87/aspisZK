# R735 sampled ABC norm

R735 proves a source-shaped chord-coordinate fact with all successful-sample
and checked-inequality conditions visible. Over any field with `2 ≠ 0`, two
distinct unit-circle pairs have nonzero squared chord norm, including the
vertical-chord case. It then instantiates the fact for two successful selected
`challenge_secure_circle_point` calls and their actual raw point-inequality
result. Finally, a successful `R203ChordDataExecution.rawData` result with
canonical encoded batch inputs has the same nonzero decoded `abc` `(b,c)`
norm.

The final focused target was
`AspisV8R19/R735SampledAbcNorm.lean` at source revision
`e61245853008f9dd911558f7b11d070f134d108c` (SHA-256
`7f9a81c71b7d290d488e90b44b0fac119259b561f18fbd29bec5136c919f38de`): exit 0, wall 1.78 s, peak RSS
3,761,568 KiB, swap 0, run `1791135046183450000`. Its three printed theorems
audit to standard axioms; the two source-result bridges also retain the
existing `core.fmt.Formatter` dependency inherited from the generated circle
interfaces. The earlier pair-only green run and the initial mechanical type
failure are retained in the evidence bundle.

This is not a full callback chronology, a proof that any specific callback
obtains both successful samples, a bridge from these coordinates to every
selected quotient image condition, or a privacy/soundness conclusion.
