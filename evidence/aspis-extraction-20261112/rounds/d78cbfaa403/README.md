# Rewrite rounds 2b and 2c merged (verifier program and Pool): gate against the frozen gate

Status: target not yet established. A record of tests and measurements; nothing in it is a proof.

## What was gated

Commit d78cbfaa403 on the candidate branch `aspis-next`: round 2b (verifier program, gated alone in
`../8ba85f1946b/`) and round 2c (the Pool program rewrites of `../../pool/README-stage2c.md`). Host tree
`src-nx5`, files sha256 d51cbdbc78fe4929bce8fd65a8280f6d460743ce01dc8c8ff9c5dd48b31fbbb1.

Script: `../../host/fv_round_checks.sh` with the intended-removals list of record
`../../host/fv_round_intended_removals.tsv` (host attempt `NX5-gate`, exit 0, wall 32:52.37, scope memory peak
4,061,450,240 bytes). Comparison base: the frozen gate `frz/c1` (commit 3d700effcab). Step list: `steps.txt`;
its last line reads "status: PASSED".

Built programs (attempt `NX5-builds`): verifier with measurement ids
33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea (the same as round 2b alone: the Pool round
does not change the verifier program); Pool 009bffb5d317765067c58cce55293b1401e8017b29a6d6fc75f766397a4747d1.

## Results

| Check | Result |
|---|---|
| Verifier crate unit tests (deployed settings with the prover) | 62 pass |
| Core crate tests | 286 pass, 2 ignored |
| Statement crate tests | 287 pass |
| Client configuration (`r1p-check`), prover and simulation tests | 15 pass |
| Program crate tests, deployed settings | 93 tests, the 25 failing of the frozen tree and no other; no base test changes outcome; the two absent tests are exactly the intended removals; 6 new tests pass |
| Program crate tests, two-transaction settings | 95 tests, 0 failing; the two intended removals pass here |
| Pool crate tests | 85 pass |
| Integration tests (nine files) | pass |
| Recorded payments, deployed Pool | settle; replay conditions hold |
| Redirect attempts, deployed, frozen and round Pool | every redirect rejected with nothing changed |
| Mutant campaign, 156,704 corrupted copies of the two recorded proofs | observed run byte-identical to the frozen gate's (156,706 lines); deployed verdicts identical; no nonzero mark |
| Worst-case runs, seven constructed payments | the settled state (post-state hash) equals the frozen program's in all seven, with the frozen Pool and with the round Pool |

## Compute

Whole transaction, LiteSVM 0.16.0, Agave 4.2.1.

Recorded devnet payments:

| Payment | Programs | Frozen | Merged commit | Change |
|---|---|---|---|---:|
| Transfer | round verifier, deployed Pool | 1,281,351 | 1,282,585 | +1,234 |
| Withdrawal | round verifier, deployed Pool | 1,287,871 | 1,289,105 | +1,234 |
| Transfer | round verifier, frozen Pool | 1,232,920 | 1,234,154 | +1,234 |
| Withdrawal | round verifier, frozen Pool | 1,239,440 | 1,240,674 | +1,234 |
| Transfer | round verifier, round Pool | 1,232,920 | 1,232,749 | -171 |
| Withdrawal | round verifier, round Pool | 1,239,440 | 1,240,811 | +1,371 |

Constructed payments, round verifier and round Pool (no marker pre-funding / one-lamport marker):

| Scenario | Frozen | Merged commit | Change |
|---|---|---|---:|
| Withdrawal at page rollover, heaviest proof | 1,258,313 / 1,262,410 | 1,259,510 / 1,263,609 | +1,199 |
| Withdrawal at page rollover, another proof | 1,247,425 / 1,251,522 | 1,248,622 / 1,252,721 | +1,199 |
| Withdrawal, nearly full page | 1,249,528 / 1,253,625 | 1,250,847 / 1,254,946 | +1,321 |
| Withdrawal, young page | 1,239,175 / 1,243,272 | 1,240,535 / 1,244,634 | +1,362 |
| Withdrawal at genesis | 1,242,797 / 1,246,894 | 1,244,090 / 1,248,189 | +1,295 |
| Transfer at page rollover | 1,239,849 / 1,243,946 | 1,239,509 / 1,243,608 | -338 |
| Transfer, young page | 1,233,894 / 1,237,991 | 1,233,712 / 1,237,811 | -180 |

Heaviest measured: 1,263,609 (frozen 1,262,410), +0.09 percent, inside the round limit of 1 percent. With the
allowance of WORST-CASE-COMPUTE.md (10,697): 1,274,306, leaving 125,694 under 1,400,000. The verifier part is the
`expand_values` cost the owner approved on 12 November 2026 ("yes to both" to the lead, "yes" to the soundness
lead). The Pool round adds little on withdrawals and saves a little on transfers.

The other Pool instructions (initialize, deposit, checkpoint) were measured by the Pool follow-up worker on the
recorded transactions (`../../pool/followup/README.md`, item 4): deposit about 137,000 and checkpoint about 150,000
compute units below the frozen Pool, initialize about 1,000 above, every final account state equal to the
deployed Pool's.

The built programs carry no function symbols, so per-function figures are instruction totals of the measurement
builds plus replays, not a symbol-level comparison.

## Not covered here

- The Pool range-check follow-up (aspis-next 4dceeaab48e) and the trace-recorder feature change (4e8dec876c7),
  committed after this gate; they are gated on their own commits.
- The privacy lead's harness and proof tables on this commit.
- Translation: this gate tests behaviour; the emission of the merged commit is a separate run.
