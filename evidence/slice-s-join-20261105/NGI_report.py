from pathlib import Path
import json,re,collections,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text())
d=J(E/'NGI_LEDGER_DELTA.json');a=J(E/'NGI_AUDIT.json');s=J(E/'NGI_SCAN.json');c=J(E/'NGI_CERT_CHECK.json');rs=sorted([J(p) for p in E.glob('NGI_L*/receipt.json')],key=lambda r:r['attempt'])
assert len(rs)==30 and all(r['exit_status']==0 and r['swaps']=='0' for r in rs)
assert J(E/'NGI_REPLAY_SOURCE.json')['exit_status']==0
metrics=dict(charged_slots=len(rs),by_kind=dict(collections.Counter(r['kind'] for r in rs)),successful=len(rs),wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=0,Kani=0,extraction=0,Rust_SBF_builds=0,scope_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean='-M7000'))
for r in rs:
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
(E/'NGI_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
log=(E/'NGI_L030/stdout.log').read_text();names=J(E/'NGI_ROOT_NAMES.json');inv=J(E/'NGI_DECLARATION_INVENTORY.json');records=J(E/'NGI_CERT_CHECK.json')['rows'];rowfunc={r['row']:r['function'] for r in records}
text='''# Coherently loaded slice S root statements\n\nAll seven roots are CLOSED under the retained hybrid ruling-(y) certificate semantics and trust inventory. These are quotations of EXISTING model-side declarations, not newly stated or re-proved native equivalence or headline security theorems. The unchanged historical source/native certificates, exact caller-domain records, complete certificate-name/owner check and selected-callee denial propagation supply their ledger association.\n\nEach block is the full kernel-loaded `#check @name` output, printed with full names, explicit arguments and universes in NGI_L030. No binder or premise is omitted. Each axiom line is the exact `#print axioms` output; universe suffixes annotate the same three standard axiom constants. NGI_AUDIT.json independently raw-walks every selected root in the same combined import. Definitions and aliases remain the committed predecessor declarations; their ownership and full reference closure passed NGI_SCAN.json.\n\nRetained: P6/D188 option-A semantic transport, std/allocator/SDK/ABI/compiler/source-to-ELF realization, RuntimePersistence, digest/H realization, RuntimeReturnData (nonempty 1..1024; emitted ASR8=792), RuntimeMemcmp and the cryptographic assumptions. L154 is a statement parameter. No trust row is added or removed.\n'''
for item in names:
 n=item['theorem'];start=log.index('@'+n+' :');m=re.search("'"+re.escape(n)+"' (?:depends on axioms: \\[[^\\]]*\\]|does not depend on any axioms)",log[start:]);assert m
 quote=log[start:start+m.end()]
 e=inv['entries'][n];module=inv['modules'][e['module_idx']];root=next(r for r in d['S_roots'] if item['row'] in r['rows'])
 text+='\n## '+root['function']+'\n\nRows '+', '.join(root['rows'])+'; CLOSED. Declaration `'+n+'`, owner `'+module+'`.\n\n```lean\n'+quote+'\n```\n'
(E/'NGI_S_STATEMENT.md').write_text(text)
cache='/home/dombarker/project-offloads/codex-cx-slice-s-join-cache-20261104';seed=J(E/'NGI_INPUT_PINS.json')
text=f'''# NGI joined slice S handoff

**Slice S: 97/97 occurrences CLOSED; 7/7 roots CLOSED under the retained trust inventory. Overall 100-bit per-attempt target not yet established.**

Branch `codex/cx-slice-s-join-20261105`. Only NGI-prefixed files and this evidence directory changed. Stage commits are local, plain, with no push or merge. Session A and sibling worktrees were not modified or read as mutable inputs.

## Exact claim and association

`NGI_COMBINED_IMPORT.lean` loads the committed NGE and NGF aggregate imports together. Their transitive imports include the actual `AspisR1.RPx_Deployed.deployed`, the admitted NFX forest and NFY forest. The predecessor chains are imported unchanged, with both copied export directories first in LEAN_PATH. No owner conflict or duplicated incompatible declaration was found; no chain was patched and no theorem was restated or re-proved. `NGI_S_STATEMENT.md` quotes the exact seven existing theorem names, owning modules and full kernel-loaded types plus `#print axioms`, suitable for the lead to quote with their hybrid-certificate qualifications.

`NGI_AUDIT.json` raw-walks {a['root_count']:,} roots using the byte-identical NEP walker. All raw axioms are standard; collectAxioms disagreements: {len(a['collect_axioms_disagreements'])}. The SAME compiled proof binary passes all eight planted/mutation fixtures; source/object/binary pins and full driver diffs are retained. `NGI_SCAN.json` covers {s['modules']:,} modules, {s['declarations']:,} declaration entries and {s['edges']:,} references: zero dangling references, incompatible owners and import mismatches. {s['compatible_cached_replicas']} compatible cached replicas are disclosed.

`NGI_CERT_CHECK.json` checks ALL 97 S occurrences, recursively enumerating {c['theorem_record_occurrences']:,} theorem records and {c['distinct_names']} distinct names BEFORE environment lookup. Every named declaration is actually present with a matching kernel owner and raw audit. No graph/name-filter omission is accepted. `NGI_CERT_INVENTORY.json.xz` preserves every original record in traversal order; `NGI_CERT_ASSOCIATIONS.json.xz` records owners and type hashes. The two inherited to_limbs occurrences TX1:059/TX2:040 have no named Lean records in their selected historical row; their existing native admission is retained without inventing theorem names.

The unchanged NFX builder exactly reproduces its historical 587-row ledger in a private sparse-read/write sandbox; `NGI_REPLAY_NFX_LEDGER.json` records all sparse input pins. The unchanged historical S source chain validates all 97 rows (`NGI_REPLAY_SOURCE.json`). Only extra checks are added. `NGI_TESTS.json` rejects 17 evidence mutations and demonstrates actual selected-callee denial from TX2:164 to TX2:219.

`NGI_LEDGER_DELTA.json` is on the reviewed NGB 599-row basis. Relative to scoped NGE+NFY credit it restores the remaining 14 S rows; S rises 83/97 -> 97/97 and roots 4/7 -> 7/7. Before {d['before']}; after {d['after']}. These are scoped counts, excluding unimported concurrent D/Pool deltas. The 12 NGB additions stay OPEN and no identity/edge is deleted. All selected-callee denials are propagated to a fixed point. No S occurrence remains QUALIFIED and no declaration is missing; see `NGI_REMAINING.md`.

## Provenance, trust and release boundary

`NGI_PROVENANCE_CHECK.json` reproduces all 82 transported predecessor bodies check-only. Imports/owner-qualified identifiers and the recorded meta-tactic name prefix remain the only changes inherited from those chains. No generator writes to predecessors occurred. Input source/export manifests are pinned once in `NGI_INPUT_PINS.json`; cache copies are byte-checked against NGE_EXPORT/NGF_EXPORT. NGE and NGF came from committed research imports at the assigned base, not WIP or sibling live files.

No trust row is added, removed or discharged. P6/D188 option-A native-contract semantic transport remains a reclassification, never removal. Retained: std/allocator/SDK/ABI/compiler/source-to-ELF realization, RuntimePersistence, digest/H realization, RuntimeReturnData (nonempty 1..1024; ASR8=792), RuntimeMemcmp and cryptographic assumptions. L154 stays a statement parameter; coherent digest/error slots are op43/op44. This is a coherent cached hybrid-certificate join, not a cold release replay or a standalone proof of the 100-bit per-attempt headline. D/Pool joins, L159/L181, final replay L187 and final trust/source/artifact audit L188 remain outside this job. Privacy and the two-transaction design are unchanged.

## Validation and resources

All **30/30 charged slots passed**, 0 Kani, 0 extraction, 0 Rust/SBF builds. By kind: {metrics['by_kind']}. Scope wall sum {metrics['wall_seconds']:.3f}s; maximum peak RSS {metrics['peak_rss_kib']:,} KiB; swaps 0. Every formal launch had fresh exit0 AND allowed:true admission, one own scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean -M7000. No timeout, memory kill, cap increase or unchanged failed-proof rerun occurred. Exact target/argv, source revision/hash, dependency and Aeneas object pins, exit/wall/RSS/swap and full axiom output are in `NGI_ATTEMPTS.jsonl` and the 30 linked receipts. New modules are import/query/audit drivers only; no new theorem was introduced. Root quotation prints universe annotations on standard axioms; the own checker strips only those annotations for constant-name comparison and retains the exact raw lines.

Two prelaunch preparation errors (no scope charged) are recorded in `NGI_PREPARATION_FINDINGS.md`: a local-to-remote cache-path interpolation and an omitted fixture seed object. Both were corrected in owned inputs, with no host infrastructure changes or weakened validation. All 30 slots were then used for the planned join checks.

Owned cache `{cache}` is retained. Selected seed: 29,979 paths, 7,556,562,490 bytes, plus the small pinned fixture supplement; predecessor caches were read-only. `NGI_CACHE_IMPORTS.json.xz`, `NGI_FIXTURE_SEED.json`, `NGI_EXPORT.json` and `NGI_CLOSURE_PINS.json.xz` pin copied inputs and actually resolved closure, including Aeneas sidecars. Restore precedence: own exports, NGE_exports_20261104, NGF_exports_20261104, NFY_exports_20261104, NFY_priority, coherent SInt2 root/objects, own fallback, pinned Lean library. No own cache or wallet/account key was deleted.

`NGI_SHIPPED_SOURCE_CHECK.json` verifies crates/ and programs/ byte-identical to frozen `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. No shipped change triggered an ELF rebuild. Pins are INHERITED, not reproduced here: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Next deliverable: lead incorporates this additive S join into the authoritative 599-row ledger alongside independent D/Pool results, then performs the remaining release gates. No S proof work remains in this job.
'''
(E/'NGI_HANDOFF.md').write_text(text)
print(json.dumps(metrics))
