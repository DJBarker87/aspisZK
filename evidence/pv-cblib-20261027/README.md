# Library callback source campaign

Branch: codex/pv-cblib-20261027. Initial candidate revision:
`bd47052f039ae2d96060acb5607fe652ebe193d4` (unmerged prover candidate).
Target not yet established. Initial rows discharged: 0.

## Rules and budget

Read pv-common.txt including rulings (a)-(g), r1p-common.txt,
local-lean.txt, the root AGENTS.md and pv-host-restored.flag.
Host restored; no restoration polls required. Env-J IDs 39600–39899;
100 charged Lean attempts, with the final three reserved for bundle audits;
10 Kani runs. TALLY.json is the running ID/budget record. IDs are consumed
before admission and never reused. Native extraction receipts are separate
from these two budgets. No local Lean invocation is authorized.

The launcher currently uses TasksMax=64, despite the historical standing
exception permitting 128. No shared infrastructure is changed.

## Source and cache identity

See source-provenance.json and source/ for pinned third-party files.
The requested cb3 `lean-objects` cache is absent after the host deletion.
No binary copied from that absent path. Every Lean run records the effective
Env-J direct import objects and hashes. Imported ProverRw modules remain
read-only. Source-revision plus per-attempt source snapshots identify uncommitted
proof additions. Cargo library versions match the candidate Cargo.lock.

## First extraction outcomes

- op212 / V234: generic wrapper extraction passes Charon, but Aeneas rejects
  structured Drop. Direct broad path mistakenly selects DynDigest.finalize
  and is rejected for Drop and escaping references. Both are retained;
  neither is a source law for Digest's blanket implementation.
- A more precise impl pattern was rejected by Charon's start-from resolver;
  the documented form requires the impl as the first path element.
- op34 / V185: native Vec.is_empty extraction reaches Vec's hidden layout,
  unsupported by Aeneas. An owned safe P6 reference is required.
- charon-source-op212-004: admission before scope permitted; go barrier
  refused aggregate reservation (60,532,195,328 bytes > 55 GiB). No compiler
  ran, no Lean/Kani budget charged. Wait at least three minutes before retry.

No desired-output premises, new trust items, runtime effects, or source
changes are introduced by these diagnostic extractions. All rows remain OPEN.

## Focused Lean preflight

39600, 39602 and 39603 failed during development of the Bool/scalar zero
transport; their diagnostic `sorryAx` lines are rejected, never credited.
The changed proof at 39604 passes with `[propext, Classical.choice, Quot.sound]`.
39601 was a zero-charge scanner race on an unrelated vanished session cgroup;
retry used next ID after more than 30 seconds. No unchanged failed proof was
rerun. `PV_CBL_VectorShape.emptyReference_eq` proves a generic reference-model
identity, not a native source law or a discharged row.

The first exact-type Kani admission was refused at 02:25:53 UTC for aggregate
reservation (60,532,195,328 bytes already reserved); no Kani compiler ran.
