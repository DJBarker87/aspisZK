# Handoff to session A (S-cone re-pins), 2026-10-21

From the lead coordinator. Short version: the soundness headline changed this
morning, and it now asks for something specific and narrow from each S-cone
re-pin.

## What changed

The user approved the oracle-decision port. The headline soundness theorem is
now `OraclePortHeadlineFrozen.final_soundness`
(`lean/OraclePortFrozenOrderHeadline.lean`; addendum "oracle-decision port
ADOPTED" in `design/C3-BIN-20261021.md`). Its only source premise is
`AcceptedRunJoin D rust`: on every run the frozen Rust verifier accepts, its
oracle log and outputs equal those of `dV_frozen`, the Lean model of the
frozen verifier, with the exact frozen multiproof order.
`design/JOIN-SPLIT-DRAFT-20261021.md` proves that this join follows from
per-cone joins plus one ordered caller join.

## What each re-pin should deliver

For each cone you own (S1–S6 and S9 per the user, 2026-10-21; the lead has S7, S8, S10, parser, multiproof, checkpoint ABI and Pool caller), the target is an
**accepted-run refinement against the matching `dV_frozen` stage**: whenever
the frozen function returns successfully on the reached inputs, its result
(and any oracle reads) equal the model stage's. The exact statement shape for
each cone is in the join-split table, and `design/CONE-AUDIT-20261021.md`
classifies what already exists and how close it is. The audit ranks S9 and S3
among the cheapest three to close next; the lead is doing the third, the
checkpoint ABI, plus the parser and multiproof cones.

Please state the refinements in **total form** where you can: for every input,
the extracted function returns `ok v` and v equals the model. Then overflow
freedom (R22) for that cone follows automatically from the lemma in
`design/R22-TOTAL-20261021.md`, and no separate overflow census is needed.

## Integration items

- **Combined import.** Duplicated `instDiscriminantErrorIsize`-style instances
  across separate Aeneas extractions block one aggregate import (10 duplicate
  names; three conflicting). A type-qualified naming fix is prototyped and
  shown to compile all cones together (`design/IMPORT-UNION-20261021.md`). It
  needs the S10 pins updated before the single final manifest replay.

## Two things the lead did that touched your work

1. Commit aab0d23d0 (2026-10-20 ~22:40, "Record R19 discharge…") swept in 23
   of your staged files from `lean-candidates/s5-p6-serializer-kani-v1-20261020/`,
   because we share the root checkout's index. Nothing was lost or altered,
   and your later commits build on them. Authorship is yours; the lead now
   commits with explicit paths only.
2. At about 09:33 the lead killed local ssh PID 33838
   (`ssh … echo <base64> …` writing a script for
   `project-offloads/s5-charon-selfid-repair-v1`). It had been hung since the
   ~08:12 network drop, with nothing running behind it on the host. Your
   separately started build-v5 run was not touched. If something was waiting on
   that command, please rerun it.

## S10 ownership lists for your acceptance (added 11:20)

S10 pass 2 assigned every reachable declaration of the frozen verifier and
Pool to a cone. The declarations it assigned to your cones (S1–S6, S9) are
listed in the S10 evidence (`evidence/s10-inventory2-20261021/`, see
`design/S10-INVENTORY-20261021.md`), with 57 ownership corrections. Please
review the lists for your cones and confirm or correct them. Your proved cone
joins should cover exactly those declarations.

## Target update (13:05)

The model now covers both transactions. The headline is
`OraclePortHeadlineFrozen2PerAttempt.final_soundness`, and its
`AcceptedRunJoin` is stated against `dV_frozen2`: stage 1, checkpoint save,
then Pool stage 2, with the six checkpoint digest reads in place. The
per-cone targets for S1–S6 and S9 are the matching stages of `dV_frozen2`.
For the non-checkpoint stages these are the same as the `dV_frozen` stages,
because only the checkpoint stage was inserted (`design/DV-TWOTX-20261021.md`).
The contract you are proving toward is `design/SECURITY-CONTRACT-20261021.md`:
100-bit per attempt, no grinding credit.

## Dependencies of the lead's cones on yours (23:35)

- **S7** needs the source `four_dots`, opening, fold and geometry joins from
  S4/S5 to finish its whole-function certificate.
- **S8** needs the source EbyKDot and relation-finisher laws, from the S3/S9
  EbyK work.
- **Every** lead cone (multiproof, checkpoint, S7, S8) also waits on S2's caller
  binding.
When these land, the lead composes them; please state their joins against
`dV_frozen2`, in total form where possible.

## After your S4 adoption (lead, 2026-10-22 12:20)

The lead re-pinned its cones to your adopted source (C3-BIN addenda 11:50,
12:05, 12:15; `evidence/lead-repin-20261022/REPIN.md`,
`evidence/s10-repin-20261022/`). S7/S8 declarations, parser, multiproof and
checkpoint items are unchanged. The adopted ELFs reproduce
(`40dc7574…`/`12cb0bc2…`/`121f3e29…`) and all 140 S10 ordering relations
survive. One item needs you: `canonical::Q::from_limbs` changed body
(`be073dde…` → `5c935940…`). It is reached by `EbyKDot::push` via `checked_q`,
so the S5 four-limb predicate/Option correspondence must be rebound (S5 is
yours; the S8 consumer is the lead's). Please state it against the new body.

## S2 lead caller interface (worker, 2026-10-22)

Additive interface: `lean/S2LeadInterface.lean`; exact consumers and statement
cross-check: `design/S2-LEAD-INTERFACE-20261022.md`; receipts and semantic field
audit: `evidence/s2-interface-20261022/`. No A candidate/evidence was edited.

Please export fixed-input witnesses for `S2CallerFacts`: `proofBytes`,
`publicBytes`, `proofSuffix`, `proofLength`, `checkpointBytes`,
`checkpointLength`, `nodeViews` (all b<2,k<3), `y1Input`, `observerNone`,
`reachedPrefix`, `callOrder`, `accountFrame`, `writtenMetadata`, `oracle`.
Proof/public snapshots must identify the externally fixed stored proof and
`tr.statement.pubBytes` at reached calls. Checkpoint save/TX2/resume must use
the same verifier-checkpoint bytes, with the actual writer→account→reader
transport proved separately. The record contains no observation/log/verifier-
output equality; see `FIELD-AUDIT.md` for every field's meaning.

Read-only inspection of your s126 worktree found the qualification now lists
**15/15** windows plus public/checkpoint roots. The important gap is the domain:
actual SDK native framing covers the bounded **decoder-error prefix**, whereas
the lead needs successful caller execution and fixed byte identities. Your
`all_buffers_frame` correctly leaves common-execution source-certificate
instantiation external. Its 58295-byte account frame must become the actual
[688,58295) suffix (57607 bytes); `proof_suffix_bytes` checks that conversion.
`LinkedFirst`/`stage1_current_call` expose existential owned buffers, not yet
the fixed external stored/public snapshots. `observer_none` and `first_success`
are useful exact owned Option/current-tx1 links. TX2 reconstructed ASF8 public
bytes, verifier checkpoint retention, runtime/source transport and account
metadata effects still require witnesses; ASQ8 bytes and the Pool checkpoint
are different carriers.

Checked composition also caught distinct extracted checkpoint/multiproof
`Digest32` types; `multiproofDigest` transports the identical implementation
fields. The total per-call multiproof oracle law implies the weaker checkpoint
success law via `checkpoint_oracle`; byte preservation proves neither law.
`compose` derives checkpoint bindings, six slot premises, S7 initial Progress
and actual S8 CallerInvariant from the independent lead S7 PushTrace. General
resumed Progress, saved-ten-state provenance and field meaning stay with the
lead cones; these are not disguised as S2 facts. No whole S2 or AcceptedRunJoin
closure is claimed.

Focused local compile passed (attempt6): exit0, 28.946s, peak RSS3.65GB,
swaps0; all six theorem audits standard-only. No further Lean compile is
needed for this handoff. No shipped source/ELF change or push.

## Import-union adapter adoption (release gate 1, 2026-10-22)

The real adapter is now `lean/ImportUnionNamedDiscriminant.lean`. It delegates
reader and instance generation to the pinned Aeneas generator, then gives the
instance the name `<fully-qualified-enum>.instDiscriminant`. It preserves the
scalar, explicit tags (including `u8 [1,2]`), and generic binders. The pinned
Aeneas library itself is unchanged. Rebuild this adapter if that library changes.

The deterministic migration tool is `tools/import-union/migrate.py` at repository
root. This worker applied its default scope only (`docs/research/**/lean/`),
including generated standalone type-bearing modules. No `lean-candidates` file
was edited. Session A should apply the **same script** to its chosen adopted
candidate roots, each explicitly listed, for example:

```sh
python3 tools/import-union/migrate.py --apply \
  --candidate-root docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-current-repin-20261020 \
  --manifest /tmp/session-a-import-union-before-after.json
python3 tools/import-union/migrate.py --check \
  --candidate-root docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-current-repin-20261020 \
  --manifest /tmp/session-a-import-union-check.json
```

Repeat `--candidate-root` for each adopted extraction. The script changes only
`@[discriminant ...]` to `@[import_union_discriminant ...]` and adds one
`import ImportUnionNamedDiscriminant`; all other bytes remain unchanged. Keep
the before/after manifest from the **first** apply; a second apply is a no-op
and produces an empty manifest. Commit the manifests with the adopted pins.
Do not migrate alternative source variants into the same environment as if
they were separate modules: one selected provider owns each Lean module name.

Compile the adapter first, then changed Types roots, then all transitive
consumers in the selected S10 manifest bottom-up using a private object overlay.
Include both `AspisR1TerminalDecoder.Types` and `AspisR1WithdrawalCaller.Types`:
their old `instDiscriminantPoolV1TransitionKindU8` collision stopped part 52 at
`ExtractedDecoderCallerBridge`. Re-pin source and object hashes and audit raw
`ModuleData.constants` across the final union, since environment enumeration
alone suppresses accepted duplicate equation theorems. Duplicate definitions
are errors; duplicate generated equation theorems with the same type are allowed.
Use the existing host caps (6G high, 8G max, zero swap), retain the cache, and
record all AGENTS formal-release fields. Keep this import-compatibility result
separate from discharge of soundness or privacy premises.

Worker receipts: `evidence/import-union-20261022/`; migration hashes are in
`migration.json`, exact-byte validation in `migration-validation.json`, and
focused adapter checks in `adapter-host/`. The final union source is
`lean/ImportUnionReleaseGate.lean`. This handoff requests Session A's candidate
adoption and S10 re-pinning; the worker does not claim those edits are done.
