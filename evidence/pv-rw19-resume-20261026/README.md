# pv-rw19 resumed validation

Read `FINAL-REPORT.md`, `summary.json`, `premise-delta.json` and
`final-verification.json` for final status. Earlier STAGE1/preparation files are
historical, compile-free drafts; all nine inherited drafts were subsequently
checked. The command-only standalone audit failed before execution at 27826;
its commands and the old component audit were checked together in the final
manifest at 27828. No further compile was launched after the 100-attempt limit.

Each numeric `*-receipt.json` includes target, status, time, RSS, swap, revision,
source/dependency hashes and printed axioms. `*-input.json`, source snapshots,
stdout, timing and admission logs retain failures and uncharged refusals.

Cache evidence distinguishes historical per-object hash matches, the rw18
frozen dependency pins, and ten legacy transitives whose object hashes were
first recorded during this continuation. All final source statements were
checked in the capped Linux environment. This is a cached component replay,
not an independent clean rebuild or a deployed-release result.
