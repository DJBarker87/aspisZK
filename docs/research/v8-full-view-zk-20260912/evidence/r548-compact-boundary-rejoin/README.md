# R548 compact boundary rejoin — scratch evidence

Target: `AspisV8R19/R548CompactBoundaryRejoin.lean`.

Final focused Lean result: run `1791072203795643000`, exit 0, wall 1.16 s,
peak Lean-child RSS 2,058,684 KiB, swap 0. The six complete `#print axioms`
reports in the final log each contain only `[propext, Classical.choice,
Quot.sound]`.

The final theorem set proves an abstract degree-27 reconstruction identity,
its nonzero-point equality characterization under an unequal boundary claim,
and rejoin at zero. It then proves equality of the recursively defined
`wireRounds`, `walk`, and `terminalGuard` values for arbitrary identical suffix
records/challenges. It does not prove Rust execution, source degree, transcript
law, probability, privacy, or security.

Earlier failed focused attempts are preserved without alteration:
`1791072150990668000` (identity/ring and equality proof),
`1791072176635238000` (identity normalization), and
`1791072190529901000` (identity normalization). Each has exact source, raw
log, and receipt under `evidence/attempts/`.
