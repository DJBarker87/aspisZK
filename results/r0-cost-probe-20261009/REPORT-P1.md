# P1′ COST PROBE — blocked before B

**Unproved cost experiment. B has not been implemented or measured.** No
soundness, privacy, or adoption conclusion is made. This is a preflight status,
not the requested completed B report. C0′ and C2–C5 have not started.

Requested base: `origin/v8-reference` at
`bedd0420705bb13e3b1c5a45f308762a736aa260`; requested branch:
`codex/r0-cost-probe-p1-20261009`. Read the P1 decision and superseding P1′
sections of `docs/research/v8-r0-rust-20261009/PLAN.md` at that base,
`R0_SOUNDNESS.md` §8, and M1's phase evidence.

The existing branch was clean at `db0577b9f` before this documentation update.
It contains the earlier P1 C0/C1 experiments, with common ancestor
`f1e5ca9de` against the requested base. It does not contain the accepted S4
implementation. The previous report is preserved byte-for-byte as
[REPORT-P1-PRE-PRIME.md](REPORT-P1-PRE-PRIME.md). Its C0 and C1 numbers are
historical P1 evidence and must not populate the P1′ cumulative table.

## Existing C0 evidence, imported without execution

P1′ C0 is **R-E4 S4: 15,078,299 / 15,070,869 verifier CU**. These numbers
come from the existing `re4/s4-diagnostic/{transfer,withdrawal}-diagnostic-1.json`
files at the requested base. Their hashes and sizes are recorded in
[p1-prime-preflight.json](p1-prime-preflight.json). No C0 measurement was rerun.

| Phase | C0 transfer CU | C0 withdrawal CU | M1 CU |
|---|---:|---:|---:|
| Semantic, combined | 2,647,122 | 2,642,844 | 427,470 |
| Semantic component: transcript / sumcheck | B pending | B pending | 140,757 |
| Semantic component: terminal including mask | B pending | B pending | 286,713 |
| prepare / ChordClaims | 968,572 | 967,918 | Not mapped |
| Merkle ×22 | 641,001 | 641,165 | Not compared here |
| V1 ×22 | 3,010,106 | 3,008,755 | Not compared here |
| V2 | 7,803,350 | 7,802,091 | Not compared here |
| Other verifier CU | 8,148 | 8,096 | Not compared here |
| **Verifier total** | **15,078,299** | **15,070,869** | Not compared here |

Semantic exceeds M1's combined 427,470 CU by 2,219,652 / 2,215,374 CU.
prepare exceeds the lead's **estimated**, not measured, 200,000-CU arithmetic
cost by 768,572 / 767,918 CU. Attribution of either excess remains unknown
until B completes. Existing S4 heap high-water is 131,032 bytes. These are
inherited measurements, not validity results for a new probe binary.

## Execution blockers

The read-only build-host preflight failed: `ssh dombarker@nuc` could not
resolve the host; connecting to the previously recorded address
`100.108.41.90:22` returned **Operation not permitted** (exit 255). The
session restricts network access and disallows approval escalation. No
remote build or measurement was launched.

The session's filesystem permission profile also makes `/Users/dominic/ZK/.git`
read-only. The existing branch's Git metadata is under that directory. No
merge, rebase, branch update, or commit was attempted. These report changes
are uncommitted. Updating the branch to the requested base and committing
evidence requires writable Git metadata.

Repository rules require SBF builds on the Linux build host in individual
scopes with MemoryHigh=4G, MemoryMax=6G, and swap=0. Local execution cannot
substitute for that required evidence. No caps were raised, no unchanged
measurement was rerun, and no build, native gate, or stack audit was run.
No implementation, reference prover, `r0/onchain.rs`, fixture, or Lean file
was changed. Only Markdown and JSON preflight evidence were written.

## Next required work

With build-host access and writable Git metadata available, reconcile the
existing branch with `bedd04207`, retaining the historical evidence while
excluding the old R91-enabled C0 and C1 from P1′. Then instrument a separate
S4 probe for B, with no optimization:

| Phase | Required breakdown |
|---|---|
| Semantic | Parse/canonical checks; transcript absorb/squeeze; 25 round checks; 10 α-round polynomial evaluations; terminal including mask; point/extra-claim handling; handoff |
| prepare | Transcript; data copy; validate_points; interpolant; chord pair; claim_prime; query sampling |
| One V1 fibre | Value decode; four dots; four inversions; fold; final_encoder |
| V2 | G; chord_weights; indicator sum; three tensor/pairing intervals; images |

B must reconcile with the imported S4 phase totals within logging cost and
be reported independently before C0′. C0′ requires both fixture byte
comparisons, all 1,894 rejection comparisons, and field-byte traces against
S4 before each changed configuration is measured. Continue in the order
C2 → C3 → C4 → C5(a), C5(b), C5(c), subject to the specified stop rules.
**C1 is excluded from measurement.** New binaries, text dumps, and
disassemblies stay on the build host; record their SHA-256 and size, and
retain one stack-audit JSON per configuration. No new artifact exists yet.

C2 adds three full degree-six records (672 bytes) after the C1 wire. Labels
0xc1–0xc3 bind the seven canonical coefficients before each E challenge.
The initial dual weight carries R0's quarter; later rounds use unscaled dual
folds, so each boundary is c0+c4=incoming and the terminal dot has four terms.
The native prover checks the dot identity after every fold. Every C1 proof byte
is preserved. All 21 new coefficient mutations replace 21 redundant later-fibre
leaf mutations per fixture; the total remains 1,894 rejections. Both fixtures
accept, and the shared field/phase gates pass. The SBF call graph has 283 linked
functions with zero reachable diagnostics.

C2 completed totals are 18,091,187 / 18,089,626 CU, heap 106,456 bytes.
All ten 1.4M runs exhaust in Semantic. This first relation implementation still
constructs the 1,024 K weights and folds them explicitly; the four-term terminal
does not eliminate that construction cost. Its measured increase is not a
lower bound on an alternative tensor-contraction implementation. No complete
reachability conclusion is drawn from this schedule. The initial driver build
failed on an encoder-validation borrow lifetime; its changed replacement and
all resource receipts are retained.
