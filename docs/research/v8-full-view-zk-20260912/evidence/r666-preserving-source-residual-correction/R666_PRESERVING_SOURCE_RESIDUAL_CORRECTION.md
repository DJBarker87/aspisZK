# R666 preserving source residual correction

Status: focused-green release candidate. Root review and promotion remain
pending. This package has not staged, committed, pushed, or replayed a target.

R664 derives the retained p2 moment identity from the exact all-beta
source-coefficient premise at beta 0, 1, and 2. R665 transports that identity
to the full 1024-coordinate source `rangeDot`, retaining all tau image-update
weights. R666 combines R660's full-support conditional residual correction,
R665's p2 equality, and R662's full indexed mask addition.

Under its explicit premises—first-fold-zero for R and G, seven plain R
coefficients zero, seven structured G coefficients zero, nonzero quarter and
scale, and the exact residual-matrix determinant—it returns a correction that
keeps all beta and all seven source coefficients zero. It also preserves the
combined full incoming G mask's 271 sparse coordinates, two stated point
functionals, and inactive balance; the correction's modeled query roots and
32 first folds are returned unchanged.

This is exact field-model algebra. It does not derive the premises from native
execution or legal same-public witnesses; it does not provide the full
214-active-row H1 construction, the actual root/determinant law, a shared
oracle law, a complete published-view simulator, privacy, soundness, or an
end-to-end security result.

Final R664 run: `1791114529542037000`, revision
`aa1a2d5823368175afbc95cf41666785973c2c18`, source SHA-256
`94bc9c27042fb2303469fccb1997fb0f185b983eac1a6945e727ec35bdef1108`, exit 0,
wall 1.77 seconds, RSS 3,306,816 KiB, swap 0; one report uses only
`propext`, `Classical.choice`, and `Quot.sound`. Its five earlier changed
failures are retained.

Final R665 run: `1791114618714744000`, revision
`93623cf50cc47bc4696b0521494170c02d0db1a9`, source SHA-256
`589868a6a751ccaa87ac9e42d3d75d83e6cd549f08bb8b6b9bd287af1d7be41d`, exit 0,
wall 1.46 seconds, RSS 3,301,880 KiB, swap 0; all three reports use the same
standard axioms subset.

Final R666 run: `1791114726938288000`, same revision, source SHA-256
`d4f29e5d11d79533505d1c9769ea171236feddcabab3082bb6eeaee2b178e0dd`, exit 0,
wall 1.28 seconds, RSS 3,296,372 KiB, swap 0; its sole report uses the same
standard axioms.

The package pins unpromoted R664 and R665 sources and their focused cache
receipts, as well as R653, R660, and R662 dependency source copies.
