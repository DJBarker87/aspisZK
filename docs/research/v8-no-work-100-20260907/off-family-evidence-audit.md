# Focused off-family evidence audit

Parent `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`; borrowed formal source
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The new files are `off-family-tail-evidence.json` and
`experiments/audit_off_family_tail_evidence.py`. The older committed
`adaptive-tail-evidence.json` is unrelated and remains unchanged.

The recorded file now contains successful current-source evidence for all
ten required targets: 51 named standard-only axiom audits, with 21 failed
diagnostics retained separately. The transfer receipt covers 23 NUC runs and
55 exact artifact versions; none is unmapped. The initially pending skeleton
was replaced only after the final `FixedC1OutsideQuery` log, manifest and
output arrived and passed the audit. No compiled result follows merely from
finding an `.olean` file, and these counts are not a security level.

## Read-only commands

From the research worktree:

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_off_family_tail_evidence.py --prepare-receipt
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_off_family_tail_evidence.py
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_off_family_tail_evidence.py --check-recorded
```

The first command emits metadata for **already transferred** NUC files. It
does not transfer files or certify a proof. Its output may be preserved as
`adaptive-tail-transfer.json` using the normal scoped file-edit workflow.
Missing artifact versions are listed explicitly and cause a nonzero exit.

The second emits the current inventory. A missing or changed endpoint remains
visible and causes exit 1. The third requires a complete current-source
inventory and exact equality with the recorded manifest; a pending skeleton
cannot pass it.
None of these commands invokes Lean, Rust, SBF, a remote job, a field search,
or the budget script's finite-support enumeration.

## What is checked

- Ten required leaves: `FoldSupportClosure`, `HighAgreementTail`,
  `MaskedCurveTail`, `OffFamilyIntersection`, `MaskedCurveRepresentation`,
  `SelectedMaskedCurveTail`, `TwoTailQueryBound`, `SelectedOutsideQuery`,
  `FixedC1OutsideQuery`, `SelectedSupportIdentification`.
- Exact current target source hash, a successful terminal exit, output hash,
  all requested named axiom audits, and only `propext`, `Classical.choice`,
  `Quot.sound` when used. Diagnostic logs containing failed/admitted results
  never supply a green endpoint.
- Darwin `/usr/bin/time -l` RSS in bytes versus GNU `/usr/bin/time -v` RSS
  in KiB, explicit zero swaps and the applicable bounded memory setting.
  Generic NUC leaves use High 5 GiB / Max 7 GiB / Lean `-M6500`. The parent's
  separately authorized first selected cached-composition checks may use
  High 8 GiB / Max 10 GiB / Lean `-M9500`, still `-j1` and swap disabled.
  This does not authorize unchanged failed generic retries at a larger cap.
  The parent later separately authorized the **changed**, import-narrowed
  `SelectedSupportIdentification` and dependent `OffFamilyIntersection` at
  the same 8/10 GiB profile after isolated native-cache import failures. The
  auditor requires recorded lower-cap failure hashes and rejects this
  exception if the successful target's source hash is unchanged. The helper
  now imports only the actual canonical V7 schedule; no job exceeds 10 GiB.
- Local imported source/olean hashes before and after the focused leaf.
  On the NUC, the run-specific manifest, actual imported overlay closure,
  source snapshots, previously checked generated imports, command and actual
  cgroup settings are retained and matched.
- Separate retained classifications for source errors, recursion limits,
  memory/time guards, provenance errors and rejected axiom audits. A later
  green result does not delete its earlier diagnostic.
- The exact three rational off-family terms, their shared rho/tail addition,
  support-averaging certificate and 40,282-byte census, independently of the
  recorded decimal display. Missing global terms remain null.
- Frozen overlap-control source/input hashes, actual observed-cache versus
  full-support outputs, failure controls and separate optimized compilation
  and host execution measurements. The old strategy search is not rerun.

Remote artifact versions are keyed by **pathname and hash**, not pathname
alone. An unrelated later pending source correction cannot invalidate a
previously checked leaf's imported closure. If a used historical source
changes, its exact saved version is required. Green sources are not thawed.

The failed `TwoTailQueryBound` NUC v2/v3 source snapshots were reconstructed
from the known small edits and checked against their original logged SHA256
values (`80ab3c52...` and `2d69e901...`). Their exact bytes are now retained as
`two-tail-query-bound-nuc-v2-source.txt` and `-v3-source.txt`; reconstruction
did not replay either failed proof and does not turn them into successful
endpoints.

## Boundaries the audit does not erase

Borrowed compiled artifacts are reused pinned cache inputs, not newly replayed
source-to-olean compilations in this continuation. Native NUC package caches
are explicitly revision-bound; the package build has not been replayed or
asserted byte-identical to a Mac package build. The new leaf's axiom audit
checks its recorded dependency set, not compiler correctness.

This evidence audit does not independently establish that a theorem's
hypotheses match the complete Rust verifier, that its bounded family can be
efficiently extracted, or that an extracted tuple is a payment witness.
Those scopes belong to `adaptive-tail-continuation.md` and the actual theorem
statements. No numeric subtotal is promoted to global V8 security, and no
work credit, protocol change or CU claim is introduced here.
