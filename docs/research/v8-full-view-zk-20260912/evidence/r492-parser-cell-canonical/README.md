# R492 parser cell canonicality evidence

The three complete source snapshots, receipts, and raw logs are preserved by
run id. `1791044361151659000` is the initial worker success; its source SHA is
`f137039bad88821f74dca4e476643ef5a4198a9d37b02b2c938d527164928b66`.
`1791044494613076000` failed with duplicate declarations. The final green run
is `1791044531454752000`, source SHA
`ab5066ac4caec99815aa578e45dff779059479ab870815c1aa63cb2d598d9eb8`, and
matches the promoted canonical source copy byte for byte.

Each raw log retains its complete `#print axioms` output and GNU-time metrics.
`SHA256SUMS.txt` covers every archived artifact. This bundle documents the
focused formal result only; it makes no native parser/source correspondence
claim.
