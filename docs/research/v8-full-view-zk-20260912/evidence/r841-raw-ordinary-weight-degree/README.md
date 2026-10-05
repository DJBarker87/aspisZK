# R841 raw ordinary-weight degree

For every source index and base-field `half`, this target proves total degree at most 60 for R738's exact ordinary `rawOrdinaryWeight` over the R745 polynomial inputs: `C half`, `(1+u*v)`, `(u*v-1)`, `-(u+v)`, `pKappa`, `pTau`, and `pZ`.

The proof composes the ordinary original-weight degree bound (58), exact `transportDual` and `extendFin1024` branches, R838's source-chord-transpose degree bound (+2 for the ABC polynomials), and all three false-branch image updates: `tau` at 1023, `tau^2*b` at 1022, and `-tau^2*c` at 1021.

It does not establish source execution, a joint-matrix degree/determinant bound, challenge distribution, native correspondence, probability, or security.

Final target `AspisV8R19/R841RawOrdinaryWeightDegree.lean`, run `1791162227186508000-e585c6c7d66f`: exit 0, wall 1.75s, RSS 3306556 KiB, swap 0. Every printed theorem has only `propext`, `Classical.choice`, and `Quot.sound`. The preceding three attempts are retained as rejected mechanical plumbing: absent dependency/inference at `9d510499b507`, ABC proof branch at `5ae24a8179d6`, and degree coercion at `63ab879ac648`.
