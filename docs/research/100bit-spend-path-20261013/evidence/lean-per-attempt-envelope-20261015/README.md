# Per-attempt numeric envelope evidence

This focused Lean target proves exact rational inequalities for the requested common envelope `B = 15 / 2^109`: the query cap, each semantic-prefix row budget, the opening cap, and the rho cap are at most B, and `33 * B < 1 / 2^100`.

Final source SHA-256: `5db0178ee41654de50c30aec4b7ce91e13f9c96207540f5b37df7222a05fc8bf` on base `6459d24bcd83bf12441b606d8031b6c9301bc320`. Attempt `per-attempt-envelope-c` exited 0 in 0:02.08 at 3591920 KiB peak RSS with zero swap under 4G/6G/0. Five public results report only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

For the q22 ratio, the proof reuses checked 22-factor descending-factorial counts before rational normalization. The other bounds use the symbolic semantic-row maximum and prior opening/rho cap theorems. These inequalities make no probability or protocol-level interpretation.
