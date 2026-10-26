# EJS env-J continuation handoff

Branch `codex/cx-envj-rebuild2-20261026`; isolated worktree
`/Users/dominic/ZK/.worktrees/cx-envj-rebuild2`. Commits local; no push.
This is the explicitly authorized incident-recovery infrastructure exception.
S2 OPEN; target not yet established. Infrastructure recovery removes zero
premises from the actual top theorem.

## Confirmed recovery results

- All twelve prior missing-import failures compile at 30800–30811 with unchanged
  source hashes and the repaired loader context.
- Historical provider hash `d7e06b9f7a29e903f7cf24c2305b80b91658dc8a86ae6aaaecca8a815f26a776`
  is attested by successful 5623; unchanged CertOwnFill passed historical 5633.
  Exact provider blob and unchanged dependent sources were restored into the
  separate `codex-cx-import-union-20261022/EJS_provider` profile. CertOwnFill
  31016 passes with `[propext, Classical.choice, Quot.sound]`. Original J/union
  source selection is preserved. Source symlinks rejected outside Lean's root
  at 31012 were replaced with byte-identical hardlinks; no proof edit.
- Formatter repair is the exact recorded `daeafff88224be0870aadb6c3bad73ae7c9375c2de9bbceb177ed2d183d6bdc5`
  source plus five archive-attested unchanged library sources. Separate
  `EJS_formatter_joint` and `EJS_formatter_union` profiles preserve their
  original generated Types variants. Joint consumer 31044 and union consumer
  31074 pass the complete printed standard-axiom gate. Historical originals
  30628/30791 and failed repair attempts remain excluded, not relabelled.
- Diagnosis: the canonical namespace mirror replaced valid reuse symlinks
  with earlier fallback objects. Union Fmt was `cd6de4ce…` while the compiled
  repair was `438c263b…`. The EJS adapter preserves valid aliases, replaces
  dangling aliases only, and guards the assigned IDs/budget. Canonical builder,
  J.json, run-joint.sh and run2.py are not edited. Complete owner/library and
  generated dependency replay resolved both consumers. The canonical builder
  alone still has the alias-overwrite behavior; preserve the EJS adaptation.
- The dependency frontier has 234 uniquely attested source hashes resolved to
  exact git blobs, 59 modules with ambiguous hashes and six unattested names.
  Eligible sources contain no sorry/admit/native_decide/new axiom declaration.
  They are restored under `EJS_missing`; only validated outputs provide missing
  objects in the two authorized recovery roots. Existing regular files are
  never overwritten or silently adopted. The original 19 unresolved selected
  hashes and 329 historical variant hash failures remain unresolved.

## New launcher smoke test and non-vacuity

`R1Z/EJS_Verification`, attempt **31075**, goes through rebuilt run-joint.sh
with allowed admission and imports `R1Z.PrivacyR1HeadlineDeployedReal`.
Exit 0, wall 2.548651406 s, peak RSS 4,202,744 KiB, swaps 0.
Source revision `fbda5d86aa33abba917a064a44f89b9ed806d625`, SHA256
`ef58bd84a0e020fd05fcc4b4793665a2a4db403d8c26cd02f6d44857b302989d`.

```
'R1Z.EJS_Verification.successor_nonzero' depends on axioms: [propext]
```

Statement: `∀ n : Nat, Nat.succ n ≠ 0`, with no antecedent and inhabited carrier
(witness 0). This is a non-vacuous infrastructure test, not a security theorem.
The two EJS diagnostic modules only print existing declarations; no theorem or
axiom is added by them. No security non-vacuity witness is added or re-established.

## Actual top theorem: before/after and ledger

`AspisR1.Rc2_Top.deployed` is byte-identical before/after, full source snapshots
`EJS_top-before.lean.txt` / `EJS_top-after.lean.txt`, SHA256
`24460608f3b6099aff4581cf34a8a3339c565a934365cf96cf480eec6e39b4fd`.
The working-tree `lean/Rc2_Top.lean` matches those bytes. Quantifiers, carriers,
failure event, conclusions, hypotheses and trust items are unchanged.
No source premise is discharged, added, renamed or bundled.

Ledger_003–005 / Cons / Rc2 atomic-leaf, quantified-family, SAME-witness and
shared-dictionary method, on unchanged source/premise JSON:

| Scope | Before T/P/C | After T/P/C | Delta |
|---|---|---|---|
| Actual application | 82 / 171 / 0 | 82 / 171 / 0 | 0 / 0 / 0 |
| Deduplicated actual + non-alias deployment | 88 / 184 / 0 | 88 / 184 / 0 | 0 / 0 / 0 |

This is a static zero-delta recount, not a fresh actual-top or frozen-release
replay. Recovered historical privacy modules do not establish the adopted
frozen3 security target or source-to-ELF refinement.

## Scope and receipt interpretation

Every compile is sequential in its own 6G high / 8G max / swap0 / tasks64 scope,
Lean -M7000. Admission stdout/stderr is retained before transfers. No cap is
raised. EventsR1P2 and SimCostOuterRetry6 are excluded and untouched. No Kani,
Rust or SBF run; no shipped file or cfg(kani) harness changes.

Per-attempt exact command, target, source/blob revisions and SHA, dependency
fingerprint, actual compiler/validation exits, wall, RSS, swaps and full printed
axioms/errors are in `EJS_attempts.jsonl` and `receipts/`. Compiler exit 0 is
separate from the full standard-axiom gate. Reuse records are distinct from
compiler attempts. Cache integrity is distinct from a coherent release replay.

Inherited, not newly reproduced ELF pins:
- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

No session A worktree/candidate or other live worker's directory is modified.
Objects/sources/journals are retained as explicitly requested for continuation.

## Final budget, integrity and resume

Pending final collection. Do not interpret this section as authorization for
additional compiles. The assigned cumulative hard limit is 1600 (800 inherited
plus 800 new), IDs 30800–34999 only, with this run guarded below 31600.
