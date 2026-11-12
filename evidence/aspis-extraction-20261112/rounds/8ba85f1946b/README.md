# Rewrite round 2b (verifier program): gate against the frozen gate

Status: target not yet established. A record of tests and measurements; nothing in it is a proof.

## What was gated

Commit 8ba85f1946bfd373f5c5d6438af70ef25f6ff8d3 on the candidate branch `aspis-next`: the frozen
commit 3d700effcab, the prover rewrite branch, round 2a (shift amounts, `CM31::inv`), the
`COPY_PATTERNS` constant, and round 2b (the verifier program rewrites recorded in
`../../onchain/README-stage2b.md`). Host tree `src-nx4`, files sha256
a63216aa53960bbdf5b2e5cc404f6a0c251d576e13f84e09f9713b596f637761.

Script: `../../host/fv_round_checks.sh` (host attempt `NX4-gate`, one slot, wall 49:48.75, scope memory
peak 4,066,070,528 bytes). Comparison base: the frozen gate `frz/c1` (tree `src-frz-a`, commit
3d700effcab). The step list is `steps.txt`.

Built programs (attempt `NX4-builds`): verifier with measurement ids
33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea; Pool
67c097f0c92341c3b210120fe9842ecbe98d2bdb8e6bdc60e4fe1d4cb2cd12d3. Both differ from the frozen ELFs, as
expected for this round. The privacy lead's builds of the same commit give the same two hashes.

## Results

| Check | Result |
|---|---|
| Verifier crate unit tests (deployed settings with the prover) | 62 pass |
| Core crate tests | 286 pass, 2 ignored |
| Statement crate tests | 279 pass |
| Client configuration (`r1p-check`), prover and simulation tests | 15 pass |
| Program crate tests, two-transaction settings | 95 tests, 0 failing; every test of the base keeps its outcome; 6 tests only in the round, all pass |
| Program crate tests, deployed settings | 93 tests, 25 failing (the same 25 as the frozen tree: two-transaction checkpoint tests that the one-transaction configuration rejects at its first stage); 6 tests only in the round, all pass; 2 tests of the base absent (below) |
| Pool crate tests | 78 pass |
| Integration tests (nine files) | pass |
| Recorded payments, deployed Pool | settle; replay conditions hold |
| Redirect attempts, deployed and frozen Pool | every redirect rejected with nothing changed |
| Mutant campaign, 156,704 corrupted copies of the two recorded proofs | observed run byte-identical to the frozen gate's (156,706 lines); deployed run verdicts identical; no nonzero mark |
| Worst-case runs, seven constructed payments | the settled state (post-state hash) is identical to the frozen program's in all seven |

The script's last line reads "status: FAILED". The cause is the two absent tests, and only them:
`r1_pool_adapter::checkpoint_tests::r15_lifecycle_requires_recorded_signer_to_upload_or_seal` and the
same test in `r1_pool_adapter_original`. Round 2b compiles the lifecycle handlers out of the
one-transaction configuration (item D of the round: no admitted instruction reaches them in either
configuration), and gates those tests the same way. They still run, and pass, under the
two-transaction settings. The replay tool's non-zero exits with the frozen and round Pools are by
design (its two-transaction control differs when the Pool is not the recorded one), as at the freeze.

## Compute

Whole transaction, the round verifier against the frozen verifier (LiteSVM 0.16.0, Agave 4.2.1).

Recorded devnet payments:

| Payment | Pool | Frozen | Round | Change |
|---|---|---|---|---:|
| Transfer | deployed | 1,281,351 | 1,282,585 | +1,234 |
| Withdrawal | deployed | 1,287,871 | 1,289,105 | +1,234 |
| Transfer | frozen | 1,232,920 | 1,234,154 | +1,234 |
| Withdrawal | frozen | 1,239,440 | 1,240,674 | +1,234 |

Constructed payments, frozen Pool (no marker pre-funding / one-lamport marker):

| Scenario | Frozen | Round | Change |
|---|---|---|---:|
| Withdrawal at page rollover, heaviest proof | 1,258,313 / 1,262,410 | 1,259,491 / 1,263,588 | +1,178 |
| Withdrawal at page rollover, another proof | 1,247,425 / 1,251,522 | 1,248,603 / 1,252,700 | +1,178 |
| Withdrawal, nearly full page | 1,249,528 / 1,253,625 | 1,250,714 / 1,254,811 | +1,186 |
| Withdrawal, young page | 1,239,175 / 1,243,272 | 1,240,401 / 1,244,498 | +1,226 |
| Withdrawal at genesis | 1,242,797 / 1,246,894 | 1,244,039 / 1,248,136 | +1,242 |
| Transfer at page rollover | 1,239,849 / 1,243,946 | 1,241,027 / 1,245,124 | +1,178 |
| Transfer, young page | 1,233,894 / 1,237,991 | 1,235,120 / 1,239,217 | +1,226 |

Heaviest measured: 1,263,588 (frozen 1,262,410), +0.09 percent, within the round limit of 1 percent.
With the allowance of WORST-CASE-COMPUTE.md (10,697): 1,274,285, leaving 125,715 under 1,400,000.
The round Pool (built from this commit; its source is unchanged, the statement crate it links is
not) gives the same figures as the frozen Pool in every scenario.

Per item, from the worker's measurement builds (`../../onchain/README-stage2b.md`): the change comes
from `compact::expand_values` (+1,386 per recorded payment, one added range check per value; every
other item is zero or negative). The ELFs carry no function symbols, so per-function figures are
instruction totals of the measurement builds plus replays, not a symbol-level comparison.

The owner approved the compute of `expand_values` on 12 November 2026 ("yes to both", to the lead;
"yes", to the soundness lead).

## Not covered here

- The privacy lead's harness, proof tables and review on this commit (its review by reading found no
  difference; the harness and tables were running).
- The merged commit d78cbfaa403 (round 2c, the Pool rewrites): gated separately.
- Translation: this gate tests behaviour, not the emission; the emission of the merged commit is a
  separate run.
