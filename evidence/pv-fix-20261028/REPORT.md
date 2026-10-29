# D422 compliance repairs

**V213 still OPEN. Replay PASSED (62002).** This is a partial compliance repair,
not a privacy restoration or a completed final-manifest replay.

Branch `codex/pv-fix-20261028`, worktree exactly
`/Users/dominic/ZK/.worktrees/pv-fix`, base
`1a3cd3de26c0129eaefd6913b34e03fde119bf1f`.
Host directory `/home/dombarker/project-offloads/codex-pv-fix-20261028/`.
Sparse checkout was extended only with `git sparse-checkout add evidence/pv-fix-20261028`.
No new proofs, theorem-statement changes, implementation edits, native scopes,
Kani, new trust items, or wallet/key operations.

## V213: exact binding and affected objects

Recount8 `CORRECTIONS8.md` rejects the original41466 admission. Its exact target is
`R1Z.PV_CB_Op109CanonicalBinding.reference_equation`; module source blob
`d8b5384c801127a367814102760d9451806f2334`, SHA256
`1c5cb8d0a25f00080c6e9dc154acb57a4abed3e0189dc749a1aa6baf3e7d5ae9`.
41466 launched about127 seconds after refusal, inside the180-second cooldown;
its object remains VOID as historical evidence.41460 failed and earns no credit.
Later imports and coherent hashes did not cure41466.

`rows/V213.md`, `rows/V213.json`, the41466/41469 receipts,
`resume-final-receipt-coherence.json`, and the pinned final source/object/import
DAG identify the whole-Result restoring theorem as
`R1Z.PV_RDCD_Op109Audit.source`, obtained from
`R1Z.PV_CB_Op109Exact.op109_source`. The helper theorem
`R1Z.PV_RDCD_CanonicalSource.reference` was41462, not41466.
The reverse import closure contains exactly these eight modules:

| Module (`R1Z.` prefix) | Pinned blob | Fresh outcome |
|---|---|---|
| `PV_CB_Op109CanonicalBinding` | `d8b5384c801127a367814102760d9451806f2334` | 62012 PASS |
| `PV_CB_Op109Funs` | `74aa4afc6080481fe307ede08b6a34b3fe540731` | 62013 PASS |
| `PV_CB_Op109Exact` | `0a929d2688786fb010ec4ff0b803beafce880449` | 62014 PASS |
| `PV_RDCD_Op109Audit` | `a7065373e002744da36da2627b99b2e27f18cd6d` | OPEN — not recompiled |
| `PV_RDCD_FinalAudit` | `59a7b410ea15a2a63460fa7fc5000a30b4913bb3` | OPEN — not recompiled |
| `PV_RDCD_FinalReplay` | `205cda94d79681cbdf1fd3102b51d513e885a2f2` | OPEN — not recompiled |
| `PV_RDCD_AllAxioms` | `fff70506804889ad9b78ab110280ef8ca1b8920e` | OPEN — not recompiled |
| `PV_RDCD_FinalManifest` | `2642cda06757f4e62d95253fa45c899d51ba4523` | OPEN — not recompiled |

`affected-order.json` retains each edge and source pin; `inherited-rdcd-fingerprint.json`
retains the original complete DAG. All recompiled V213 sources byte-equal their
original pinned blobs. They were uploaded from those git blobs, without edits.
62004–62011 rebuild the binding's prerequisite chain;62012 freshly recompiles
41466's binding, followed by62013 Funs and62014 Exact, in dependency order.
Their existing axiom directives report only standard axioms. This repairs the
binding object itself, not the entire requested restoration.

The original rdcd `lean-objects` directory had been deleted. Before compilation,
44 of69 recorded project objects were missing and15 remaining resolutions had
different hashes. They were neither substituted nor accepted as the old cohort.
The isolated preflight records every missing/mismatched object and every available
source/import hash. Matching-object searches for the missing RDCD canonical and
op107 audits found no retained copies. Rebuilding prerequisites used the remaining
budget. The full restoring theorem and four aggregate consumers are not freshly
compiled. No old41466-derived object is credited or imported by a new audit.

The exact missing private V213 audit closure after this run is:

- `R1Z.PV_CB_Op107Exact`
- `R1Z.PV_CB_Op107Funs`
- `R1Z.PV_CB_Op107Transport`
- `R1Z.PV_CB_Op107Types`
- `R1Z.PV_RDCD_CanonicalSource`
- `R1Z.PV_RDCD_Cast194`
- `R1Z.PV_RDCD_Op107Audit`
- `R1Z.PV_RDCD_Op109Audit`
- `R1Z.PV_RDCD_Option194`
- `R1Z.PV_RDCD_OptionBinding`
- `R1Z.PV_RDCD_ShiftBound`
- `R1Z.PV_RDCD_ShiftLiterals`
- `R1Z.PV_RDCD_Wrapping194`

The prepared `PV_FIX_V213Audit.lean` inspection-only wrapper was **not run**.
Therefore the requested focused statement-and-axioms audit of
`PV_RDCD_Op109Audit.source` against fresh objects is **not established**.
Source inspection confirms the retained complete Result/Option statement has
no canonical-input restriction, but source inspection is not a fresh kernel audit.
No unchanged theorem proof failure was observed; the prerequisite failure62003
was an environment/object-resolution error quoted below. The exact reason V213
remains OPEN is the missing coherent prerequisite/consumer closure, unperformed
restoring-theorem audit, and exhausted15-attempt budget.

## RDEAC replay: minimal name repair and result

The failed61199 source is retained in the inherited evidence. Relative to that
exact text, this repair adds only:

```lean
open PV_RDEAC_EndpointInstance (endpoint)
```

`replay-before-after.diff` records the one-line repair. All theorem statements and
proofs are otherwise byte-identical to failed61199. The base already contained
an uncompiled multi-site qualification and two stale comments; the tracked diff
replaces that pending version with the one-line repair above.

**Replay PASSED at62002**: `physical`, `owned`, `source_tail`, and `source_factor`
all compile and each prints exactly `[propext, Classical.choice, Quot.sound]`.
`out-62002.log` contains the complete output. No theorem proof or statement was
modified to obtain this result. V178/V181 remain SUSPENDED: successful focused
replay does not discharge their diagnostic-provenance/deployment obligations.

**The requested single replay invocation was not met.** Two charged compiler
invocations,62000 and62001, failed before elaboration because my private external
input overlay omitted Lean companion files and then IR data. These were my input
errors. I corrected them and restored the original RDEAC environment before62002;
no admission failure, cooldown bypass, cap change, or proof change was involved.
The distinct failed inputs and environment hashes are preserved, not disguised as
successful or uncharged attempts. All three invocations count toward15.

## Admission, input changes, and verification

Exactly15 Lean compiler attempts,62000–62014:12 PASS,3 FAIL; zero native scopes,
zero Kani. Zero reservation refusals and zero new ruling(t) violations.
Each invocation checks admission in the same Python command that launches its
scope, requiring both exit0 and `allowed:true`. The existing in-scope barrier
checks admission again and verifies the actual cgroup limits. Raw admissions,
barriers, output and time logs are retained. No refusal occurred, so the180-second
cooldown was never triggered; the wrapper enforces it job-wide if triggered.
One own scope ran at a time. IDs were scanned against other privacy-job receipt
names and shared `sent.txt`; initial overbroad matches inside hashes were false
positives, corrected to numeric ID fields before any scope launched.

All scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; Lean-M7000,
-j1, timeout900. Peak RSS2,842,488KiB; every reported swap count0.
5673 external primary objects were hashed against the coherent replay authority
before the first compiler. Original companion inputs were linked read-only;
none was rebuilt. `preflight.json` records the complete inherited project source,
object and direct-import fingerprints and both original environments. RDEAC reused
its verified304-module closure plus Axioms/Statements receipts61197–61198.

The final RDEAC environment has the original LEAN_PATH prefix. RDCD adds a verified
read-only external-object prefix before its unchanged original environment to
avoid a shadowing missing `Aeneas.olean`. Every prerequisite actually consumed by
the new binding/Exact objects was rebuilt here at its pinned source, with recorded
actual import hashes. Incomplete or mismatching cached project closures were not
reused. `env-<ID>.json` preserves each exact effective env-J input; run2 prepends
this job's own object directory. `companion-inputs.json` and `ir-inputs.json`
record auxiliary input identities.

62000→62001 changed companion-file inputs;62001→62002 restored the original
RDEAC environment and IR paths.62003→62004 added the complete verified external
prefix, including IR companions. These are recorded environment/input changes,
not unchanged failed-job reruns. No shared launcher, reservation script, source,
object, other worktree, or other job directory was modified.

All compile receipts use source revision
`35d6cd2434` (full value in `revision.txt`), with each exact source path, git blob
and SHA256 independently recorded. Setup scripts changed during input repairs;
this is not a claim that every historical wrapper invocation used a clean HEAD.
The exact compiler command, effective environment and actual dependency hashes
are retained per attempt in `attempts.json` and the raw receipts. No full regression
or final manifest was claimed.

| ID | Target (`R1Z.` prefix) | Exit | Wall | Peak RSS KiB | Swap | Axioms output |
|---|---|---:|---:|---:|---:|---|
|62000|`PV_RDEAC_EndpointReplay`|1|0:00.05|88920|0|not reached|
|62001|`PV_RDEAC_EndpointReplay`|1|0:00.42|711232|0|not reached|
|62002|`PV_RDEAC_EndpointReplay`|0|0:01.26|2675492|0|4 standard theorem output(s)|
|62003|`PV_CB_Op109Types`|1|0:00.11|190960|0|not reached|
|62004|`PV_CB_Op109Types`|0|0:01.16|2636480|0|none emitted by unchanged target|
|62005|`ProverRwFullExternalTypes`|0|0:01.37|2642912|0|none emitted by unchanged target|
|62006|`ProverRwFullTypes`|0|0:06.67|2819360|0|none emitted by unchanged target|
|62007|`ProverRwFullExternalFuns`|0|0:05.07|2842488|0|none emitted by unchanged target|
|62008|`PV_CB_Op109Transport`|0|0:01.14|2633860|0|none emitted by unchanged target|
|62009|`PV_CB_Op109RefTypes`|0|0:01.09|2636692|0|none emitted by unchanged target|
|62010|`PV_CB_Op109RefFuns`|0|0:01.14|2638236|0|none emitted by unchanged target|
|62011|`PV_CB_Op109RefTransport`|0|0:01.15|2633880|0|none emitted by unchanged target|
|62012|`PV_CB_Op109CanonicalBinding`|0|0:01.10|2637884|0|1 standard theorem output(s)|
|62013|`PV_CB_Op109Funs`|0|0:01.51|2663764|0|none emitted by unchanged target|
|62014|`PV_CB_Op109Exact`|0|0:01.18|2641664|0|1 standard theorem output(s)|

Full #print axioms lines are in `attempts.json` (`axioms_full`), and all raw output
is retained. An unchanged module with no audit directive is explicitly recorded
as having no emitted audit result; this is not an axiom-freedom claim.

Exact retained compiler failures:

**62000**

```text
/home/dombarker/project-offloads/codex-pv-fix-20261028/rdeac/sources/R1Z/PV_RDEAC_EndpointReplay.lean:1:0: error: failed to open file '/home/dombarker/project-offloads/codex-pv-fix-20261028/external-objects/Init.olean.server': No such file or directory
```

**62001**

```text
/home/dombarker/project-offloads/codex-pv-fix-20261028/rdeac/sources/R1Z/PV_RDEAC_EndpointReplay.lean:1:0: error: missing IR data file for module Init.Prelude
```

**62003**

```text
/home/dombarker/project-offloads/codex-pv-fix-20261028/rdcd/sources/R1Z/PV_CB_Op109Types.lean:3:0: error: object file '/home/dombarker/project-offloads/codex-cx-prover-commit54-20261023/objects/Aeneas.olean' of module Aeneas does not exist
```

## Claims and next deliverable

Before/after theorem statements and hypotheses are unchanged. No privacy-headline
premise was removed, added or changed. E1/E2, real RunJoin/native carrier/world,
client proof-account routing, L1/L2/L3, compiler/primitive adequacy, and T exactly
`entropy_law/entropy_kernel/observation` remain. V213 native restoration credit
stays suspended. No Kani result is used. No release implementation changed, so no
ELF rebuild was performed. The privacy target is not established.

Next: retain/reuse this pinned private build cache, authorize enough unchanged
prerequisite recompilations to finish the missing Op109Audit closure, rebuild the
five remaining affected modules in `affected-order.json` order, then run the
focused restoring-theorem statement/axioms audit. Do not consume the old aggregate
objects or treat62012's fresh binding alone as restoration.

Commits are path-limited to this evidence directory and the replay wrapper; see
`COMMITS.txt` and `git log --oneline 1a3cd3de26..HEAD`. No push was performed.
