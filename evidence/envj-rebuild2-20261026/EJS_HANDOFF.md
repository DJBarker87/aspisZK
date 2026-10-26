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

## Later recursive package and parser recovery

The first recursive phase added 637 uniquely source-attested dependencies.
Eleven further exact hashes were recovered from historical git blobs. The
committed retained CompPoly inventory pins upstream revision
`4165a87dd9a9ede48ee4dc5b4fe825604b8bb932`. Its immutable source archive matches
all eleven recorded hashes. Seventy-six needed additional ancestor sources
also match this repository's historical package snapshot blobs byte-for-byte;
`EJS_comppoly-plan.json` records both provenance chains. Only the needed closure
is restored; no package version or proof body is improvised.

The EJS parser recognizes `import all M`; the canonical parser had treated
`all` as a dependency. A later missing transitive wrapper was isolated at
31435. The launcher refused the unchanged fingerprint before compiling at the
next ID; the original guard text and log-retention qualification are in
EJS_refusal-31436.json. The eventual retry fingerprints the actual newly
available transitive object/source hashes and passes. No refusal is counted as
a compiler attempt, and the duplicate guard is never bypassed.

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

**800/800 additional Lean attempts used, IDs 30800–31599; 1600 cumulative. 0 Kani. Next unused ID: 31600. No further compile is authorized.**

Compiler exit 0: 796; printed standard-axiom gate not rejected: 787; peak RSS 4,677,612 KiB; total swaps 0. Resource failures: 0. Additional object reuse records: 79. These are cache measurements, not premise discharge.

Remaining original resolved source entries unattempted: 669; profile entries unattempted: 501. EJS_resume-plan.json contains exact source SHA/blob/revision/path records, latest failures and pending dependency names; original 19 selected and 329 historical unresolved hashes are retained. Eleven additional source hashes were resolved by read-only git-blob history traversal and staged for continuation without substituting any original unresolved selection.

Integrity snapshot: 2833 source entries; 1538 latest successful compiled object entries; 108 reused object entries. Source mismatches 3; latest-object mismatches 2; reuse mismatches 0. Exact paths/hashes are in EJS_integrity.json. Shared-file drift is preserved, not overwritten or adopted.

- Source drift `/home/dombarker/project-offloads/aspis-joint-20261019/sources/AspisR1ProverCommit/Types.lean`: expected `1cffcca7f5d3ff42d8f477e2b5e46c8bbded355d72d0d85ae76a64e99b5bb384`, observed `d3b7106ad143be82d8512a65de5dfbc0a9dfa2aa6e16a60f5507b7c6a06aa5d4`.
- Source drift `/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z/BuilderAdmissionExtracted.lean`: expected `bbddadb0e25cf688dcc625ff0a623fdb83b1a80fe3e9d4d798025123f74e12ef`, observed `19d637faebb2eb5aa0d8e2f66e0e3f9b2f31e5ff036594c1da8ff0fe254753b6`.
- Source drift `/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z/PrivacyR1HeadlineV2.lean`: expected `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`, observed `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16`.
- Object drift `/home/dombarker/project-offloads/aspis-joint-20261019/objects/R1Z/BuilderAdmissionExtracted.olean`: expected `38f63c049275222c616bddfcf33437044433921d89adffba7bf1a0068974ed6b`, observed `3d8cb34b1106832e2c5eef7b8dba846e78aef92f323db618c33792afc20fb36c`.
- Object drift `/home/dombarker/project-offloads/aspis-joint-20261019/objects/AspisR1ProverCommit/Types.olean`: expected `1baa307cfe6d62566beae15b082a7caf52082ffb16b10b503a4e1d847f779472`, observed `80105a7feb92aa607c98f0323e7e20600c9625ee88243039a4efa34ee24df1bf`.

The canonical builder and launcher/environment/driver pins are recorded in EJS_integrity.json. All owned build work is terminal. No frozen manifest, actual-top axioms replay, SBF or release conclusion is claimed. Use the EJS adapter source/manifest selection for a future explicitly budgeted continuation; do not resume the unguarded canonical mirror behavior. Retain the four authorized recovery roots and all EJS profile objects/journals.
