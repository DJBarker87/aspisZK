# Collision provenance — 1791151232440308000

The receipt records R788 target and source SHA-256
`4e12daa43d188c1513b0c4f56d5e0e0dd900bf3b346480c30225e4aefba461e1`.
The shared `aspis-focus-1791151232440308000.source.lean` was overwritten by
concurrent R791 and has SHA-256
`6edc63fa2051e9e5ed88be5ddff80d6a4cc2830f0802d804717e919fcbf2eb64`.
It is unrelated to R788 and must not be used as its source snapshot.

`source-after-failure.lean` was copied after later R788 edits and has SHA-256
`b90bbdc0c1cc94299a6fda72ed099e7669aa0ba636f2d4f38116b0637cb74f44`.
A reconstruction from recorded edits was attempted without guessing semantic
content; its SHA-256 is
`311264dbc03ed1f67225eada57f17fbc05d96b2f68da185a6f3cb9dddfe2bb87`,
which does not match the receipt. Therefore the original failed source is
unavailable and the reconstruction is explicitly non-evidentiary.

The independent final green run uses source SHA-256
`327d55b8ad26f736a88db12d6c23b166451001db69c70e286ece299f29da3381` and
is unaffected by this collision.
