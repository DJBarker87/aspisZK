from pathlib import Path
import json,subprocess,hashlib
D=Path('evidence/pv-b3q-20261029');v=json.loads((D/'verification-summary.json').read_text());old=json.loads(Path('evidence/pv-b3p6-20261028/resume14/link-status.json').read_text());new=[]
for r in old:new.append(dict(**r,b3q_status='UNCHANGED: inherited model/context status retained; complete changed-function native/caller/dependency association remains OPEN',b3q_scope='changed functions excluded by D500'))
(D/'inherited-link-status.json').write_text(json.dumps(new,indent=2)+'\n')
status='''# D500 link status

V244/op227 remains OPEN. The table records existing-link instances, source inspections and concrete comparisons. Native source/caller/dependency obligations remain explicit. No link was redefined, no privacy endpoint/deployment premise was removed or added, and T, V370/D381/D386, the simulator and the byte-plus-side-channel observer are unchanged.

| Existing PV_B3P link | Compiled instance / evidence | Status |
|---|---|---|
| `PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14` | Source-step dossiers and typed instances for conversions, Result/Option, scalar comparison/Clone, array/slice view and restoration, M31/U32 slice equality, wrapping/checked arithmetic, bit-count wrappers, Range and four-slot iterator metadata. See `frozen-manifest.json`, `catalogue-status.json`, `std-source-association.json`, `index-source-association.json`. | **PARTIAL; full concrete catalogue OPEN.** Every captured entry is reported; the 80-entry conservative source union is not an exact-cone/omission certificate. Panic formatting, pointer/dependency coverage and full caller association remain open. |
| `PV_B3P_Groups14227.PV_B3P_Link_D188` | `PV_B3Q_D188.direct_store_link`, complete borrow/direct and continuation laws; array mutable-port binding. `d188-function-status.json` accounts for all 29 generated mutating declarations / 27 Rust function families, 41 mutable borrows and 343 direct updates. All back functions are visibly applied, all updated states consumed, no dropped suffix flagged. 96 new plus 52 inherited comparisons; new mismatched-result control fails at exactly one intended output. | **Store instance PROVED; requested per-function restoration inspection/comparison PASS.** Complete changed-function native/caller association remains a separate OPEN obligation. |
| `PV_B3P_Binding14227.PV_B3P_Link_matrix_stores` | `PV_B3Q_Matrix.deployed_store_link`; full target/other-row/other-channel frame laws; all-prefix observation; injective nine-word observation; `PV_B3Q_MatrixIntermediate.matrix_link_with_intermediate`. Actual source-private Prepared type/constructor used, with observer erasure recovering the original function byte-for-byte. 14 matrix cases / 126 entry comparisons (13 distinct input tuples) compared directly to emitted models, including raw noncanonical words and wraparound. | **Storage-port instance PROVED; requested direct matrix association checks PASS.** Comparisons are finite validation. The complete source-shaped intermediate Result equality is universal in the declared port types. Whole callback/native-caller equivalence is not claimed. |
| `PV_B3P_Groups14227.PV_B3P_Link_slice14` | `PV_B3Q_FourSlice.source_link`; arbitrary success/fail/div callbacks, constructor/count alignment, region preservation and terminal None checks. Native actual-QM31 mutable iterator positive/negative controls. | **Four-slot port instance PROVED.** Complete pre-inline pointer/dependency catalogue remains OPEN. |

The partial conjunction has the explicit same-port joint witness `PV_B3Q_Combined.joint_scope_witness`. It supplies no complete deployed-catalogue or endpoint decomposition claim.

## Formatter obstruction

`FORMATTER-FINDING.md` records both issues. The strengthened native check forces `Arguments::as_str=None`, verifies the rejected numeric payload is `17`, observes Rust `Err`, and has a matched failing success expectation. The pinned numeric model prints an always-Ok body. Its axioms audit reports `Aeneas.Std.core.fmt.Formatter`, while that carrier independently prints as Unit with no axioms; this pinned-cohort/audit-metadata discrepancy is not waived. Actual-function diagnostic attempts 70267/70269 remain quarantined. Only the standard-only quoted-port refutation `PV_B3Q_FormatLiteral.literal_instance_false` is credited. No op227/endpoint counterexample or actual formatting reachability claim follows.

## All inherited changed-function links

The 36 original function-link statuses are preserved in `inherited-link-status.json`. None acquires a complete native association here. The inherited 79 conservative application candidates / 41 BOUND = 40 reclassification-bound + 1 own-1 remain unchanged; standard-library ports are not added to that numerator. `scope-refinement.json` records impossible lexical edges without pruning the legacy link obligations or claiming exact reachability.

| Link | Inherited status | D500 native status |
|---|---|---|
'''
for r in old:status+='| `'+r['link']+'` | '+r['status'].replace('|','/')+' | OPEN; unchanged |' + chr(10)
(D/'GROUP-STATUS.md').write_text(status)
res='''# D500 residuals and handoff

**The target is not established.** No privacy endpoint/deployment premise was removed, weakened, added or moved into T. All side-channel, simulator and observer standing is retained. No source under crates/ or programs/, PV_B3P source/link definition, foreign branch/worktree or shared source was edited. No push, merge or wallet/key operation occurred.

The complete concrete standard-library/dependency catalogue remains OPEN. `catalogue-status.json` names every conservative capture entry and its local proof port or remaining gap. A complete deployed source-cone/omission certificate was not obtained. Pre-inline pointer/dependency bodies and panic/formatting reachability remain explicit. The false generic always-Ok interpretation is checked on a valid rejecting formatter; it is not a counterexample to op227. The actual pinned formatter also fails the permitted-axioms audit, with a reported dependency whose current exposed definition is Unit. No library object was rebuilt, substituted or its audit suppressed.

The affected full-catalogue step stops on that checked source/model obstruction and the pinned-cohort audit discrepancy. This is not budget exhaustion: 19 Lean attempts and 14 native scopes remain. The two unaffected requested evidence gates are completed: all inventoried mutating helper restoration checks, and direct actual-private-type intermediate matrix comparisons connected to model storage laws. Their generic link instances, full-result port laws and explicit partial joint witness compile. Whole changed-function/native-caller/dependency closure remains open.

Next deliverable: resolve/re-pin the formatter cohort under the lead's authority and either prove all formatting/panic paths unreachable in the actual guarded source cone or supply faithful writer/error-state models. Then complete the remaining pointer/dependency catalogue and instantiate the complete existing std family. Source bounds/model success alone and optimized absence do not supply the missing native-source reachability/caller association. The live b3p6p changed-function work remains separate and untouched.

## Validation and retained failures

81/100 Lean attempts: 57 compile exits zero, 24 rejected. Fifty current accepted frozen modules comprise 47 focused sources plus the three audits; 96 audited theorem names use only propext, Classical.choice and Quot.sound. The two compiling actual-formatter diagnostic versions are quarantined, not credited. Earlier successful superseded sources and diagnostic-only modules are not silently promoted to accepted proofs.

16/30 native scopes: eight positive checks, seven deliberate failing controls, one initial harness compilation error (by-reference versus by-value arguments), fixed under changed source in a fresh scope. Earlier literal-format controls are outer-formatting checks only; the strengthened placeholder controls establish numeric source-path selection. Zero Kani. There were 20 refused resource gates; all accepted subsequent launches followed the full cooldown (minimum measured recovery 180.640 s). No void compile, unchanged failed-source resubmission or out-of-range charged ID was found.

Every receipt records target, exit, wall time, RSS, swap and exact revision; theorem axioms are preserved in full stdout and `verification-summary.json`. Caps were MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean -M7000. External 5,673-object preflight preceded the first compile; 137 inherited cohort objects were rechecked unchanged before audits. The initial missing source-authority companion was resolved through the inherited tracked resolution/hash chain, without rebuilding or editing its source. The single final frozen-manifest replay was not repeated after the later changed native formatter test.

`generator-checks.json` reproduces 22 fixtures/native suffix files exactly in isolated scratch. Frozen Rust prefix/snapshot copies intentionally preserve their original trailing whitespace and exact byte hashes; a blanket diff-whitespace check reports those copied lines. Accepted Lean/prose/tool edits are checked separately. No executable or compiled Lean object is delivered. Build-host caches and all retained task data remain in the job-private host directory.
'''
(D/'RESIDUALS.md').write_text(res)
audit=[next(r for r in v['lean_receipts']if r['attempt']==a)for a in [70297,70298,70299]]
final='''# D500 V244 residual associations

Branch `codex/pv-b3q-20261029`, base `15819d2768`. **V244/op227 remains OPEN; no privacy endpoint premise removed.**

- **Std/dependencies: PARTIAL.** Concrete source-step/actual-model instances compile, including the emitted M31 comparison trait. Complete catalogue/reachability remains open. A rejecting numeric formatter returns Err while the inspected model always returns Ok. The pinned function also reports a disallowed formatter dependency despite that carrier printing as Unit/no axioms. Actual-function proofs are quarantined; only the standard-only literal-port refutation is credited. See [finding](FORMATTER-FINDING.md), [every captured entry](catalogue-status.json).
- **D188 checks: PASS.** All 29 mutating declarations, 41 borrows and 343 updates reviewed; 96 new and 52 inherited comparisons. The existing store link has a compiled instance. Full changed-function/caller association remains separate.
- **Matrix checks: PASS.** Actual private Prepared type/constructor observed before reconstruction; all nine entries matched in 14 matrix cases, including raw noncanonical inputs. Universal port/intermediate equality, storage, readback, frame, prefix and injectivity laws compile.

[Every link/status](GROUP-STATUS.md), [residuals](RESIDUALS.md), [receipts and verification](verification-summary.json).

| Target | ID | Exit | Wall s | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|---:|
'''
for r in audit:final+='| '+r['module']+' | '+str(r['attempt'])+' | '+str(r['exit'])+' | '+str(r['wall_seconds'])+' | '+str(r['peak_rss_kib'])+' | '+str(r['swaps'])+' |' + chr(10)
final+='\nAudit source revision: `'+audit[0]['source_revision']+'`. Axioms: 96 theorem names, standard set only. One frozen replay. 81 Lean attempts, 16 native scopes, zero Kani; all capped, no void launch or unchanged failed-source retry. The catalogue step is blocked on the checked formatter obstruction/cohort audit, with 19 Lean attempts unspent. T and V370/D381/D386, observer and side-channel standing are unchanged. No shipped/PV_B3P source change, push, merge or key operation.\n\nHistory: `git log --oneline 15819d2768..HEAD`; snapshot in [git-log.txt](git-log.txt).\n'
(D/'FINAL.md').write_text(final)
(D/'git-log.txt').write_text(subprocess.check_output(['git','log','--oneline','15819d2768..HEAD'],text=True))
print('FINAL words',len(final.split()))
