# R15 first-query address audit

2026-09-19; research base `3721572af6494f0bfed495ed851de97e7cb264f2`;
underlying source `9e432896a4e1515efebe940b71fd9b4f9f009189`.

## Verified result

The optional read-only `r15_query_audit.rs` records concatenated inputs to
the controlled host hash callback, stopping at the first q22 return. No
answers, source sampler, production paths, or witness masks are changed.
The fixed-function override was disabled for this run. This is the duplicate
witness-0 fixture under SHA-256, not an entropy-backed random-oracle experiment.

Observed before the first query cut:

```
lengths={33:114,42:3,43:1,50:4,52:2,53:524286,59:1,60:3,62:2,
66:1,75:1,79:2672,83:512,110:1,131:1,138:262144,141:1,182:2,
184:1,220:262144,280:262145,437:262144,467:20,499:4,579:1,
1426:2,4130:1,6335:1}
unique33=62 nonce_calls=1 nonce_fresh=true
output_fresh=true advance_fresh=true
```

The sampler made six 33-byte calls, all fresh, in three output/advance pairs
using the same old state within each pair; there were no other callback input
lengths during this segment. Ten semantic rounds checked and the host accepted
the complete 39,346-byte proof, with zero stress nonce attempts.

The proof SHA-256 is
`8901a810a17d5ecc5ec1f35941c7b806e05a4d529f6b58aa3d67abe337ea34ad`,
identical to the prior unaudited SHA locate-0 proof. This checks that this
instrumented execution preserved its observable proof, not all executions.
Binary SHA: `46c56e28eeb1c0591d48caedca5b8d6f4828f3fc7b253de602878e69e9ffe14c`.
Audit module SHA: `a7908b1245b61b83dbbd56560f1c7f8bb6485b0990c7cbe67d273912080e0070`.

## Execution accounting

Same pinned offline release build settings as the complete-host report;
one Cargo job, target directory `target/r15-query-audit`.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Audited host release build | 0 | 95.86 | 557760512 | 0 |
| SHA witness-0 audited execution | 0 | 24.44 | 211763200 | 0 |

Results were captured in tool command output (build session 7400, execution
session 74093), not a persisted full log. Retained stage:
`/tmp/aspis-r15-host.drHYn9/query-audit-source`; proof directory:
`/tmp/aspis-r15-host.drHYn9/query-audit-run`. Enable audit with
`ASPIS_R15_QUERY_AUDIT=1`; unset oracle-table, stress-scan and live/complete
context variables. No Lean file changed; compilation/axioms audit does not
apply to this Rust diagnostic.

The strengthened controlled-host analyzer also passed on the existing four
executions without repeating them: every serialized pre-query field was
unchanged between SHA and fixed-function runs within each witness world.
These are byte ranges `[0,423*16)` and `[441*16,697*16+76)`; the intervening
three relation polynomials are produced after the query cut. Both wire-reader
unit tests passed. Neither comparison asserts equal prefixes across witnesses.

## First unproved proposition

Lift observed freshness to a universal source-bound probability statement.
For a lazy random function, the last nonce absorb must be unqueried given
the complete prior query history; subsequent query states must avoid prior
33-byte input prefixes. The audit counts only calls routed through this
callback and only this execution. It cannot prove exhaustive source call
coverage, nonce uniqueness for all attempts, or an adversary-query bound.

Even a valid fresh-address coupling would establish only the query law at
this cut. Reach probability, later failures, retry policy and publication
must be accounted for separately before the ideal q4/q6 mass becomes a
distinguishing advantage. The raw separator is real, but this audit supplies
neither a production attack probability nor a privacy repair.
