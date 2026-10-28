# D370 current disposition — checked N3 counterexample

Target not yet established. Successful canonical preparation can retain raw
M31(P) at C1[0][444]; native masking preserves it and N3 rejects it, whereas
the same-public M31(0) case passes the exact-body guard diagnostic. The actual
secure prover entry with OS entropy returns Err(Semantic) on the bad case.
Work stopped under the explicit counterexample rule, with 97 Lean attempts
unspent and no new Kani. V352/V354/V357/V360 remain OPEN/P; zero premises
removed, added, weakened or changed. Frozen implementation and HonestInput
are unchanged. Current evidence and accounting:
[resumed finding](resume-d369/D370-FINDING.md),
[state reconciliation](resume-d369/RECOVERY-D370.json),
[native receipt](resume-d369/canonical-n3-probe5/receipt.json).

The earlier dispositions below are historical and superseded by this finding.

---

# Current disposition after D355/D356 recovery

Target not yet established. Resume allocation exhausted: 72/72 Lean attempts
(55 pass, 17 fail), zero new Kani. Including prior work: 140 Lean, six Kani.
Final corrected-closure audits 44897/44898/44899 all passed with standard
axioms. Both exact-carrier fixtures are audited. V352/V354/V357/V360 remain
OPEN/P; no endpoint premise removed or weakened. Recovery launched no runs.

The current detailed report, complete attempt inventory, recovery receipts,
remaining obligations and stop reason are in
[RECOVERY-D356.md](resume-d355/RECOVERY-D356.md),
[RECOVERY-D356.json](resume-d355/RECOVERY-D356.json) and
[RESULTS.json](resume-d355/RESULTS.json).

The earlier allocation's report below is retained as historical evidence;
its missing audit/ID-allocation status is superseded by the current receipts.

---

# L2C D355 continuation — target not established

Branch `codex/pv-l2c-20261028`, worktree exactly
`/Users/dominic/ZK/.worktrees/pv-l2c`. Candidate base `e461dca06a`;
D355 handoff `d95d7236cd`. The conflict-free authorized runjoin merge already
contained runjoin24–29; no second merge was needed. Full candidate history:
`resume-d355/commits-from-candidate.txt`; continuation history:
`resume-d355/commits-d355.txt` (proof-source revision d8ce511a00).

**V352, V354, V357, V360 remain OPEN/P, bucket b. Zero endpoint/deployment
premises removed, added, changed or weakened. Target not yet established.**
T remains exactly entropy_law, entropy_kernel, observation. Observer, simE,
HonestInput and frozen Rust are unchanged. No checked honest-input guard
counterexample was found. The raw-P diagnostic below is not an honest input.

## Proved and audited

`PV_L2C_HonestCaller.identification`, `returned_bank`, `builder_sound` use
precisely ConsumerBoundary25.HonestInput: admission, actual full compiler return
matching cached payload, Checked and frontier canonicality. Both original
fixtures, including the concrete proof field, pass FixtureAudit. This is
compiler/decoded-trace transport, not the missing transport to every guard.

N2/N4: OwnedBalance and ScalarBalance prove complete extracted Result/table
returns with the mutation restoration retained. RowEnumeration and
SelectedDense relate ascending traversal to the excluded sum.
ExtractedGuard.padding_result proves the actual owned QM31 balance return
and both raw rejection predicates false on arbitrary canonical sampled tables
and an inactive dependent row. ScalarCanonical proves preserved raw ranges.

The script-checked balance cut is **structural (K-1 substitute)**, scoped to
length-1024 M31/QM31 balancing with an in-range inactive dependent row.
`resume-d355/balance-structural.json` records twelve checked native/reference
bodies, the row constant, every control/representation difference and its
Lean law. The earlier optimized native differential is reused unchanged:
128 complete same-input output comparisons, 128 changed dependent writes,
30.654 seconds, 639696896 bytes sampled aggregate RSS, zero swap. It is finite
validation, not honest-fixture or whole-site proof. No observation-trace
refinement is asserted for the owned reference.

N3: actual extracted M31/CM31/QM31 parsers accept concatenated scalar byte
encodings of arbitrary canonical words, retaining copy, Result and Option
branches. This does not prove native QM31 write_le_bytes roundtrip or raw
compiler column canonicality. CanonicalityBoundary proves why equality after
field projection cannot supply raw range: raw P and zero decode identically.

N5: HonestHelper proves total and inactive decoded helper sums on every exact
honest compiler input, without assuming the desired sums. HonestValidity
uses the existing NoPole condition, with no new bad event. N6: HonestSumcheck
proves decoded prepared-oracle initial/chain/terminal laws on that carrier.
These are decoded/model results, not native helper/inverse/oracle provenance.

## Validation and stop

The corrected public/private import parser was used. Final combined audit
44897, exact-carrier fixture audit 44898 and focused replay 44899 passed.
`resume-d355/final-closure-check.json` matches all 1456 selected objects,
complete direct/transitive import fingerprints, source authorities and
toolchain. h4 external preflight preceded compilation. All successful printed
axioms are subsets of propext, Classical.choice, Quot.sound.

`resume-d355/RESULTS.json` records 72 charged continuation Lean compiles:
55 passed, 17 failed; zero remaining; zero new Kani. Together with the prior
68, this is 140 total Lean compiles. One refused admission consumed zero
compiles and was retried with the same ID 44800 after cooldown. Attempt
44834 mistakenly reused stale resolution text; it remains a charged failure.
The wrapper now rejects stale tracked sources. No memory cap increase or
killed-job rerun occurred. Per-target raw receipts record target, exit, wall,
RSS, swap, revision/source/import hashes and axioms.

Stopped on compile-budget exhaustion. Native honest sampler/table/geometry
transport, raw C1/D canonicality, helper materialization/inverse boundary,
native oracle/interpolation/running claim, and E1/E2 stream/failed-prefix
coupling remain P. Next: prove these transports, starting with the sampler
and returned raw-bank range invariant. See PREMISES.md and SITES.md.

No crates/programs edits, pushes, deployment or wallet/key operations.
Pinned private host cache is retained for dependent replay; no further
compile or unchanged full regression is requested or claimed.
