# Strict import-wide axiom audit

**No reachable nonstandard axiom was found.** Both raw constant-dependency
walks agree with their roots’ `#print axioms`: exactly `propext`,
`Classical.choice`, and `Quot.sound`. Every root imports 105 other axioms, all
unreachable from both roots (144 distinct declarations across the two forests). The strict logical-axiom audit obligation is
closed for these separately pinned compiled forests.

## Scope and method

This packet audits the separately pinned L188 roots
`AspisR1.RPx_Deployed.deployed` and `AspisR1.JHx_Joint.source`. It addresses
missing obligation 3 in `evidence/native-l188-20261028/NDJ_RELEASE_MANIFEST.md`.
It does not establish the overall release security target.

`NDP_Audit.lean` enumerates every `ConstantInfo.axiomInfo` in the kernel
constant map with exporting disabled, resolves each declaration's defining
module through `getModuleIdxFor?`, and records its universe parameters, full
pretty-printed type and exact kernel expression. It independently scans all
loaded modules' serialized constant tables and requires equality of the two
axiom-name sets. No axiom is filtered by namespace, generated status, intended
use or apparent harmlessness.

The root's actual module closure is computed from the imported module-header
DAG. Extra imports needed only by the metaprogram are explicitly marked and
excluded from the root inventory. Every imported module, including modules
containing no axioms, is recorded in the Lean stdout logs.

The raw dependency walk starts at the named root and exhausts a worklist of
constants occurring in declaration types and values. `value? true` includes
opaque proof bodies. Inductive constructors are added, matching Lean's axiom
collector; constructor/recursor types are inspected as ordinary constants.
Already visited constants prevent cycles. A missing reachable declaration or
module is fatal. This is syntactic constant-dependency reachability, without
unfolding or reducing concrete arithmetic terms. It does not substitute
module-import reachability for proof dependency reachability.

The resulting axiom set must equal Lean's `collectAxioms` output (which may use
imported summaries). Each root also has its own `#print axioms` line. Compressed
sorted visited-name files provide independently checkable membership and
nonmembership evidence. `NDP_validate.py` decompresses and hashes these files,
checks every emitted axiom's membership, recomputes the import closures, checks
the printed sets, and joins both forests without silently merging differing
axiom declarations.

## Provenance and interpretation

The task cache is
`/home/dombarker/project-offloads/codex-cx-axaudit-cache-20261028`.
Its `objects/` and `joint_objects/` were copied from the read-only L188 cache;
no source object was changed, linked in place, or deleted. The own cache is
retained. `NDP_verify_seed.py` verifies every copied artifact, including private,
server and IR companions, against the predecessor's manifest SHA256 and size.
The original manifest and source/object provenance remain in the L188 packet.

This is an audit of declarations in pinned compiled objects, not a fresh
recompilation of their source dependency closure. Source template text that is
not in the actual imported compiled module is not a logical declaration in
this environment. All actual imported `FunsExternal` modules are scanned by
both enumeration paths; their per-module axiom counts are also listed in the
final JSON. No external-template exception or namespace whitelist is used.

The two roots retain separate coherent predecessor forests. Their historical
combined-import duplicate-declaration failure is retained in
`evidence/native-l188-20261028/NDJ_IMPORT_FINDING.md`; this task does not repair
or claim a compatible shared environment.


## Results

| Root | Modules | Constants visited | Dependency references scanned | Imported axioms | Reachable axioms |
|---|---:|---:|---:|---:|---:|
| RPx_Deployed.deployed | 12,712 | 115,256 | 5,743,676 | 108 | 3 standard |
| JHx_Joint.source | 15,068 | 885,779 | 15,050,073 | 108 | 3 standard |

Each root imports 108 axioms. The union contains **115 distinct names and
147 distinct module/name/type declarations**: 101 names are shared, 14 names
are forest-specific, and 32 shared names have differing type expressions.
These differing declarations are retained separately, never silently merged.
Category (a) contains the three shared standard axioms; category (b) contains
144 distinct declarations (112 names), with complete negative reachability
evidence for both roots; category (c) is empty. `NDP_AXIOMS.json` contains every declaration's module, name, type,
universe parameters, exact type expression, import membership, reachability,
classification and evidence references. No imported axiom has been accepted
merely because it is classified (b).

The inventory includes `sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`, low-level `lc*` and `Quot.lcInv` declarations, Aeneas
opaque-type/target/test declarations, and generated native-decision axioms.
All are category (b). In particular, an imported `sorryAx` declaration is not
evidence that either root uses `sorry`; its absence from both exhaustive
visited sets is checked directly.

| Defining module | Axioms per root |
|---|---:|
| AspisR1PublicPreparation.Funs | 48 |
| AspisR1RecordParser.Funs | 18 |
| AspisR1PrefixAggregateParser.Funs | 18 |
| Init.Prelude | 10 |
| Init.Core | 5 |
| Aeneas.Std.Core.Atomic | 2 |
| Aeneas.Std.Core.Pin | 2 |
| Aeneas.Std.String | 2 |
| Aeneas.Std.Core.Panic | 1 |
| Aeneas.Command.Decompose.TestsRec | 1 |
| Aeneas.Tactic.Step.StepArraySpec | 1 |

Each root includes six FunsExternal modules. Four are common:
`AspisR1AdapterReconstruct.FunsExternal`,
`AspisR1TerminalDecoder.FunsExternal`,
`AspisR1WideToBytesSource.FunsExternal`, and
`AspisR1CircleFallback.FunsExternal`. The headline forest additionally imports
`RPz7_WAdm_Fissioned_FunsExternal` and
`RPz7_AspisR1CircleSampleWrapper_FunsExternal`; the joint forest instead imports
`WAdm_Fissioned.FunsExternal` and `AspisR1CircleSampleWrapper.FunsExternal`.
Each of these eight imported compiled modules contains zero axiom declarations.
This is an enumeration result, not a decision to skip templates.

The variant distinction is substantive. For example,
`AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug.fmt._native.decide.ax_10`
proves the string-length bound for `"NonCanonical"` in the headline forest and
for `"Length"` in the joint forest. Both are unreachable. The JSON records the
exact two types and their forest memberships; these are not interchangeable
compiled declarations. This finding reinforces the retained separate-forest
qualification and does not contradict either root's accepted axiom set.

## Execution receipts

Successful release-root audits used source revision
`9b61497fba330b6ed678fb570b29618380000ac6`, with dirty wrapper bytes captured
and SHA256-pinned in each attempt's `sources/` and `receipt.json`. The unchanged
generic helper was compiled separately in NDP_R002. The exact toolchain is
`leanprover/lean4:v4.32.0`; full absolute commands and dependency fingerprints
are in the receipts. Each command used `lake env lean`, `-j1`, and disabled
asynchronous elaboration.

| Attempt | Exact target | Exit | Wall seconds | Peak RSS KiB | Swaps | Caps / Lean heap |
|---|---|---:|---:|---:|---:|---|
| NDP_R002 | NDP_Audit.lean | 0 | 0.926284 | 1,587,248 | 0 | 6G/8G / -M7000 |
| NDP_R003 | NDP_Preflight.lean | 0 | 0.820228 | 1,581,496 | 0 | 6G/8G / -M7000 |
| NDP_R004 | NDP_Headline.lean, incorrect log namespace | 1 | 23.575041 | 6,261,540 | 0 | 6G/8G / -M7000 |
| NDP_R005 | NDP_Headline.lean | 0 | 17.432785 | 6,335,160 | 0 | 6G/8G / -M7000 |
| NDP_R006 | NDP_Joint.lean, import heap failure | 134 | 49.613719 | 7,169,948 | 0 | 6G/8G / -M7000 |
| NDP_R007 | NDP_Joint.lean | 0 | 36.363324 | 8,870,164 | 0 | 14G/16G / -M15000 |

Every scope had MemorySwapMax=0 and TasksMax=64. Admission receipts are retained;
only one scope ran at a time. NDP_R007 is the one delegated joint import-only
exception documented in NDP_AGG16_DECISION.md. No other raised-cap attempt ran.

NDP_R001 never started Lean: the task orchestration raced the asynchronous
cache copy before its runner had been copied. This own-input error was fixed
by awaiting the copy and using a fresh attempt identifier. NDP_R004 completed
the audit but had an independent mistyped log-marker namespace; it is rejected
as final evidence, preserved, and replaced after that source correction. No
unchanged successful full audit was repeated. Six Lean compiles were used out
of the budget of twenty; no dependency rebuild or package-wide replay ran.

Both successful #print results are:

```
'AspisR1.RPx_Deployed.deployed' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
'AspisR1.JHx_Joint.source' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## Trust boundaries and remaining work

No hypothesis was discharged, retained as a new axiom, added, or changed. No
existing proved module, implementation, frozen artifact or security contract
was edited. Accepted logical axioms remain precisely the three standard
axioms. Imported nonstandard declarations remain present and inventoried but
are unreachable from both audited roots.

Trust still includes Lean's kernel, import mechanism and metaprogram APIs,
the pinned toolchain and compiled predecessor objects, and the ordinary
receipt/hash machinery. This axiom audit does not validate arbitrary imported
declarations' proofs afresh. Explicit theorem hypotheses, named runtime/SDK/
allocator/oracle/native-refinement assumptions, fixture scope and release
artifact identity retain exactly their L188 qualifications. Axioms and those
trust boundaries are different obligations.

The overall release target is **not yet established**. This packet supplies
missing obligation 3 only; the lead must integrate it into the release manifest
without dropping the remaining L188 obligations or the separate-forest
compatibility finding. No new coherent combined-root replay is claimed.
