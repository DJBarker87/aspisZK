# NCZ composition-ledger handoff

Branch `codex/cx-native-compledger-20261028`. No push or merge.
The requested data ledger and validator are delivered. This is an evidence
composition audit, not a new native bridge or a deployed security theorem.
The 100-bit per-attempt target, privacy and two-transaction design are unchanged.
No grinding/work-normalisation credit or new trust item is introduced.

## Delivered and counted

- `NCZ_LEDGER.json`: every one of 345 TX1 and 242 TX2 inventory occurrences;
  434 unique frozen functions. All 587 body spans independently hash-match
  frozen revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
- Local qualified bridge coverage: TX1 106 conditional,237 OPEN,2 quarantined;
  TX2 107 conditional,133 OPEN,2 quarantined. Total213 conditional,370 OPEN,
  4 quarantined occurrences. Unique120 conditional,312 OPEN,2 quarantined.
  CLOSED/unconditional0; whole functions covered only by trust0. The digest
  VALUE, RuntimePersistence and semantic-transport trust are separate rows.
- `NCZ_LEDGER.md`: summary and ranked critical frontier. Minimum reachability
  cover133 terminal OPEN SCC representatives; highest-impact OPEN rows start
  M31::reduce_u62 (40 dependent inventory rows), PreparedQm31Multiplier::new
  (34), weights::field (31). These are rankings of the conservative static
  inventories, not a measured runtime critical path or a sufficient proof set.
- `NCZ_validate.py`: independently reconstructs rows, exact inventory edges,
  source hashes, evidence/receipt hashes, feature/re-credit overlays, coverage,
  hypotheses and graph frontier. Ordinary validation never rewrites output.
  `--write` deliberately regenerates derived artifacts after reviewed changes.
- `NCZ_SUPPLEMENTAL.json`: explicit reviewed association recipes for the later
  NCO/NCP/NCC/NCF/NCV contract/reference packets outside the NCS index. Exact
  native verdicts are checked; restricted/partial proofs retain their domains.

Baseline merged snapshot `1d7752908191642fc8383c99bbadfb46fab8850c`.
Discovery includes5215 top-level merged/legacy evidence and design reports,
205 attributed claims, and SHA256 pins for7363 artifacts, including596 receipts.
These numbers describe inspected evidence, not additional proof closures.
Sparse files are read from immutable Git objects; present worktree files and
current committed objects must agree. New merged reports require an explicit
snapshot refresh. No other worker's worktree or live candidate was accessed.

## Interpretation and remaining obligations

Every local claim keeps its original domain and physical/source/library
qualifications as named hypotheses. Lower conditions are named separately,
including DigestEncodeCanonical/Raw, DigestDecode, TransferEncode,
WithdrawalEncode and checkpoint DriverEstablishedDomain. Every real/conservative
call edge has a caller-owned domain obligation, named required hypotheses and
an explicit discharge slot. Packet-internal theorems retain their original
credit; this audit does not invent a new per-edge same-execution certificate.
Consequently all587 composed-status entries remain OPEN. This distinction
prevents promoting local bridge counts into complete execution correspondence.

NCS's feature/body audit is overlaid with KNG's23 restored property associations
and KNF's static local-leaf support. The old Option<fn> receipts remain
quarantined. Both transaction occurrences of verifier::mark and release
observer remain quarantined. The old LPm checkpoint route is recorded as
superseded by KNE's reached-S2/final_len64/weights64 route. NCO's two scalar
contract leaves add qualified local credit. Later NCP/NCC/NCF claims are
retained but get no additional deployed credit where a per-crate feature
association has not been independently linked; independent NCS/KNG-qualified
claims on the same functions retain their credit. NCV's144-byte identity and
policy predicates are components, not whole decoder/cohort closures.

The original NCF ghost-pointer policy controls remain invalid; NCV's separate
ordinary policy predicate does not repair them. KMX/KMZ windows, ambiguous
multi-root associations, model-only joins, timeouts and failed drafts never
become whole-body bridges. Exact KMX patch SHA256:
`bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
Coherent dictionary digest/error slots are op43/op44. Owner amendment fifth
is a P6/D188 tool-trust **reclassification**, never premise removal.

Four unresolved historical pointers are findings rather than valid citations:
NBN_K002,NBN_L004,NCA_K001,NCF_L001. The last is already an unresolved submission
in its own packet. No missing pointer supplies selected credit. Cited artifacts
must exist and match; there is no fallback to an unrelated historical source.
The validator checks explicit structured facts and pinned audit assertions;
it cannot interpret arbitrary prose as a theorem or discover an unencoded
semantic contradiction. A report hash/corpus change fails pending review.

## Validation and budget

Fourteen mutation/positive checks pass (`NCZ_tests.py`,
`NCZ_TEST_RECEIPT.json`): open hypothesis, open call domain, missing bridge,
forged receipt hash, missing citation, quarantined selection, contradicted
feature association, changed/missing committed evidence, worktree deletion,
changed present bytes and newly merged report corpus are rejected. Tests use
in-memory mutations/mocks only; no other lane's evidence is edited.

The final ordinary validator recomputes the entire delivered ledger and summary.
Exact command, target, exit, wall, peak RSS, swap, source revision/dirty source
hashes and dependency fingerprint are in `NCZ_FINAL_RECEIPT.json`; raw timing
and output are `NCZ_FINAL_TIME.log` and `NCZ_FINAL_RESULT.json`. Python
mutation tests have their own equivalent receipt. Axioms: not applicable,
no new Lean theorem or module. Inherited proof/axiom logs are pinned evidence,
not newly replayed results. No formal release result is claimed.

Budget used **0/10 Lean status checks,0/0 Kani**. All587 assigned function
statuses are resolved as ledger entries, not security obligations discharged.
No missing status question remains that a Lean compile would settle. Each
remaining proof/domain/native obligation is enumerated per member/edge in
JSON; these need native same-execution/caller association, feature evidence,
or the stated source/runtime/ELF transport, not a status-only compilation.
No new proof work is authorised by this ledger allocation. Thus unused status
attempts are not a reason to replay unchanged green modules or launch Kani.

All work was local, read-only Python/Git inspection except this lane's NCZ_
files. No host scope, Rust/Kani/Lean compiler, solver, SBF rebuild, library
object replacement, cache seeding/deletion or key/account operation occurred.
The existing SInt2 closure manifest is pinned as input; no host LEAN_PATH is
used. Only the assigned sparse evidence path was added to sparse checkout
(after the initial staging refusal); sparse checkout was never disabled.
Validator hardening added current-commit/corpus comparison, exact receipt-source
checks, feature/overlay consistency, semantic control-result checks and explicit
per-row feature/source pins. No shared launcher/infrastructure was modified.

No assumption is discharged or added. All runtime/SDK/TrustedStd/P6/P7/D188,
canonicality, caller-domain, effects, source-to-ELF and two-transaction
qualifications remain as cited. Next deliverable: a lead-reviewed per-edge
same-execution domain-discharge certificate, starting from an actual independent
OPEN function on the ranked frontier; link its exact theorem/receipt and prove
carrier alternatives before claiming composed closure. Source-to-ELF and the
final release audit remain separate gates.

No shipped-file change triggered an ELF rebuild. Inherited pins, not reproduced:
- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Stage commits: `8cd82027e6` scope/policy; `7760dfc376` ledger/validator;
final validation/handoff commit follows this report. All remain local.

Final validation: exit0,13.46s wall,678912KiB peak RSS,0 swaps.
Mutation checks: exit0,7.428225s wall,966432KiB peak RSS,0 swaps.
All7363 artifact pins and596 receipt pins validate; all authored changes pass
`git diff --check`, all files are below20MiB, and the shipped-source diff is empty.
