# Devnet rent accounting and recovery

The finalized audit before recovery accounts for the user's 10 SOL:

| Destination | SOL |
| --- | ---: |
| Original immutable verifier | 4.785405720 |
| Original immutable Pool | 2.666070360 |
| Original immutable Registry | 0.984265240 |
| Other isolated test accounts | 0.513648960 |
| Retained payer | 1.042884477 |
| Difference spent outside retained balances (transaction fees) | 0.007725243 |
| Total | 10.000000000 |

All three ProgramData accounts have authority `None`. They were deployed
with `--final`. This removes both upgrade and close authority; retaining the
program identity keypair cannot restore it. Their 8.435741320 SOL cannot be
reclaimed with the loader close instruction. This irreversible rent consequence
should have been communicated explicitly before deployment. The selected
registry authentication requires immutable deployments, but that requirement
does not make their rent refundable.

Reference: [Solana program immutability](https://solana.com/docs/programs/deploying#make-your-program-immutable).
The original three loader buffers are absent: deployment already refunded
them. The original Pool/Registry tooling has no supported general account-close
instruction for its test-state PDAs. No production account or key was inspected.

Two superseded SPL source accounts were empty and controlled by the retained
synthetic source authority. Their mint bindings, zero balances, initialized
state, ordinary non-native token type and absence of another close authority
were checked live. They were closed through the SPL Token CloseAccount
instruction in one exact simulated-and-confirmed TxV1 transaction, refunding
the original payer. No token was burned or transferred; all keys remain local.

* Gross rent returned: **0.002976880 SOL**.
* Transaction fee: **0.000020000 SOL**.
* Net returned: **0.002956880 SOL**.
* Finalized payer balance: **1.045841357 SOL** at slot 495666234.
* Confirmed transaction CU: **348**; declared limit: **1,200,000**.
* [Refund transaction](https://explorer.solana.com/tx/4Kj9PNSy2LgFKJpFPD2B4xUF7EXksbtERgmwh6eHTx8gC35fN89QBPL9HcmpzL2nemkUwcp38TeXfh2xtdH3eVMm?cluster=devnet).

`reclaim_empty_sources.py` is the bounded recovery command. Full before/after
assertions, live ownership audit and confirmation are under
`evidence/live-checkpoint-fix/`. Prior snapshots remain evidence of their
original observation times. The current fresh source account is unaffected.
This recovery does not cover the new program rent; live redeployment and the
genuine positive atomic transfer remain pending funding.
