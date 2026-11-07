"""Assemble supporting-work receipts without promoting any Pool row."""
from pathlib import Path
import json,hashlib,re,shutil,subprocess
E=Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=[J(p)for p in sorted(E.glob('PCM_L[0-9][0-9][0-9]/receipt.json'))];ex=[J(p)for p in sorted(E.glob('PCM_E[0-9][0-9][0-9]/receipt.json'))]
assert len(lean)==200 and len(ex)==10
assert [r['attempt']for r in lean]==['PCM_L%03d'%n for n in range(1,201)]
features=J(E/'PCM_DEPLOYED_FEATURES.json');supp=[]
for r in lean:
 if 'deployed_resolved_packages'not in r:
  context=dict(attempt=r['attempt'],context_only=True,changes_original_receipt=False,scope_compiles_Rust=False,deployed_resolved_packages=features,source='Inherited exact NKZ deployed feature resolution, PCM_DEPLOYED_FEATURES.json',feature_sha256=H(E/'PCM_DEPLOYED_FEATURES.json'))
  (E/r['attempt']/'PCM_CONTEXT.json').write_text(json.dumps(context,indent=1)+'\n');supp.append(r['attempt'])
parents={'PCM_E003':'PCM_E002','PCM_E005':'PCM_E004','PCM_E007':'PCM_E006','PCM_E009':'PCM_E008'}
for r in ex:
 name=parents.get(r['attempt'],r['attempt']);pins=J(E/(name+'_pins.json'));assert pins['resolved_packages']
 context=dict(attempt=r['attempt'],scope_compiles_Rust=r['attempt']not in parents,resolved_packages=pins['resolved_packages'],source=name+'_pins.json',source_sha256=H(E/(name+'_pins.json')),frozen_lock_before=pins['lock_before'],frozen_lock_after=pins['lock_after'])
 assert context['frozen_lock_before']==context['frozen_lock_after']
 (E/r['attempt']/'PCM_CONTEXT.json').write_text(json.dumps(context,indent=1)+'\n')
standard={'Classical.choice','Quot.sound','propext'};roots=J(E/'PCM_AUDIT_ROOTS.json');results=[]
for i,g in enumerate(roots['groups']):
 v=J(E/'PCM_audit'/('proof'+str(i))/'validation.json');assert v['validated']
 assert sorted(z['root']for z in v['results'])==sorted(g)
 for z in v['results']:
  assert set(z['walked_axioms'])<=standard and z['equal']is True
  results.append(dict(root=z['root'],walked_axioms=z['walked_axioms'],collect_axioms=z['collect_axioms'],equal=z['equal'],receipt='PCM_audit/proof'+str(i)+'/validation.json'))
assert len(results)==146
scanrows=[json.loads(l)for l in (E/'PCM_audit/scan/loaded_scan.jsonl').read_text().splitlines()];assert J(E/'PCM_audit/scan/validation.json')['validated']
scan=dict(scope='SUPPORTING_CLOSURE_ONLY',attempt='PCM_L197',exit_status=0,modules=len(scanrows),dangling=sum(len(r['dangling'])for r in scanrows),canonical_duplicate_owners=sum(len(r['duplicate_owners'])for r in scanrows),import_mismatches=sum(not r['imports_match']for r in scanrows),cached_replicas=sum(len(r['cached_replicas'])for r in scanrows),algorithm='PCM_SCAN_EQUIVALENCE.json')
assert not(scan['dangling']or scan['canonical_duplicate_owners']or scan['import_mismatches'])
(E/'PCM_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n')
fx=J(E/'PCM_audit/fixtures/validation.json');assert fx['results']==J(E.parent/'ledger25-20261111/NMQ_audit/fixtures/fixtures.json')['results']
full=J(E/'PCM_audit/fullimport/validation.json');assert full['exit_status']!=0 and not full['validated']
for r in lean+ex:
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
for r in J(E/'PCM_SPEC_FREEZE.json')['sources']:assert H(E.parent.parent/r['path'])==r['sha256']
resources=[{k:r.get(k)for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits','cgroup_memory_peak_bytes']}for r in lean+ex]
audit=dict(status='SUPPORTING_RAW_AND_SCAN_PASS_REQUIRED_COMBINED_IMPORT_FAILED',supporting_only=True,row_credit=0,parent_consumers=0,security_target_established=False,headline='AspisR1.RPx_Deployed.deployed',budget=dict(kani=0,lean_link_audit_used=200,lean_link_audit_limit=200,extraction_used=10,extraction_limit=10,remaining=0),stages=dict(specifications='FROZEN_47_SPECS_61_PINNED_FILES',map='170_SLOTS_60_MISSING_CHILD_LEMMAS_110_OPEN',instances='PARTIAL_6_COMPILED_GROUPS_NO_FULL_GATE',routes_top='COMPILED_SKELETON_AND_RECORDED_PARTIAL_ROUTES'),required_gate=dict(target='PCM_COMBINED_IMPORT',attempt='PCM_L198',exit_status=full['exit_status'],passed=False,diagnosis='NMK_CompleteFold is one of the 47 prohibited-origin objects; clarification pending; none copied. PCE combined object and NMX/NMS library delivery gaps also remain.'),supporting_combined=dict(module='PCM_SUPPORT_IMPORT',attempt='PCM_L191',exit_status=0),raw_axioms=dict(new_roots=146,standard_axioms=sorted(standard),all_raw_standard=True,collect_disagreements=[],same_binary=J(E/'PCM_AUDITOR_PIN.json'),results=results),fixtures=dict(same_binary=True,same_eight_results_as_NMQ=True,attempt='PCM_L180',results=fx['results']),scan=scan,retention=J(E/'PCM_audit/retention/validation.json'),final_checks=J(E/'PCM_audit/final/validation.json'),release_pins=J(E/'PCM_RELEASE_PINS.json'),source_unchanged=True,elf_rebuild=False,trust='Option A native contract semantic transport remains P6/D188 reclassification, never removal. RuntimePersistence retained. RuntimeCpiAccountView/ReturnData/Clear named only; RuntimeCpiReadonlyEntry7 PENDING/UNUSED. L154 statement parameter. No unconditional Root0 or new hash/readonly axiom.',repairs=['Own elaboration/import/collector/input repairs retained in PCM_ATTEMPTS.jsonl','L194 interpreter scan hit Lean memory threshold; optimized native scanner L195/L197 kept caps and algorithm unchanged','L196 lacked32 canonical expected-import entries; L197 uses source-derived hashed baseline, validation unchanged'],scope_totals=dict(lean_passes=sum(r['exit_status']== 0 for r in lean),lean_nonzero=sum(r['exit_status']!= 0 for r in lean),lean_wall_seconds=sum(r['wall_seconds']for r in lean),extraction_wall_seconds=sum(r['wall_seconds']for r in ex),peak_rss_kib=max(int(r['peak_rss_kib'])for r in lean+ex),swaps=0,timeouts=0,cgroup_oom_kills=0,interpreter_memory_limit_stops=1),early_feature_context_supplements=supp,resources=resources)
(E/'PCM_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Explicit disposition for every slot and route; no zero-Kani excuse for Lean work.
m=J(E/'PCM_MAP.json');routes=J(E/'PCM_ROUTES.json')
s='''# PCM remaining work

Budget exhausted:200/200 Lean/link/audit scopes,10/10 extraction scopes,0 Kani. Supporting work only; no Pool row credit or parent consumer. The required full gate FAILED, not CONDITIONAL/CLOSED. Own supporting imports,146 raw ax2 roots and NFX canonical scan pass separately.

The 47 prohibited-origin objects remain absent (PCM_BLOCKED_CONTEXT.json); the combined import stops at NMK_CompleteFold. The requested clarification received no answer. Never infer approval or seed entry5. The supplied LIB bundle lacks the newer concrete LIBB/NMX/NMS object delivery; LIBB_PoolLib.library nevertheless exists on research and is the canonical assignment for all20 PoolLib fields. Its V0 module12/13 remains WAITING, not an open leaf to duplicate here. PCE_COMBINED_IMPORT also needs unchanged PCA objects not in the selected closure.

Six compiled groups: Registry (five fields), Deployed (two IDs), TerminalSource, AccountSource, PdaSource, GraphCompositions. Source-carrier groups retain complete deterministic model graphs and original own-input domains, but their PCM/RSL carrier/error/state/effect maps are unproved. The PDA environment adapter must identify the SAME headline Env.pda occurrence, not create another oracle. PoolAccounts and NoteSource drafts are text only and excluded from accepted imports/audits. Every unfilled field stays a named parameter; there is no relation-as-model, False domain or success-only replacement.

The missing mathematical adapters and full observation folds need Lean/representation work, not necessarily Kani. This job cannot launch another scope. OPEN native ownership rows need their future authorized direct hybrid owner campaign, same-argument CLOSED callees and proven caller clauses. Zero Kani is not presented as the reason for stopping Lean work.

## Every unfilled slot

| Slot | Classification | Remaining / named parameter |
|---|---|---|
'''
for r in m['slots']:
 note=r.get('remaining')or r.get('needed_lemma')or r.get('discharged_by','')
 if r.get('canonical_library_assignment'):note+='; concrete canonical term '+r['canonical_library_assignment']+'; object/import delivery still required'
 s+='| '+r['slot']+' | '+r['classification']+' | '+note.replace('|','/')+' |\n'
s+='''
## Top

PCM_Top.check compiles against literal RSL.PoolLib and EVB.top_splitB_full. Owners.Spec has the full328/330/327 specifications. Payload and assemble explicitly retain23 existing top bridge fields. The function from those owner proofs to the physical verifier-entry/CPI interfaces is UNPROVED. Pool:330 is not TAS verifier TX1:330. No row-number coercion is available. Same-occurrence NMN_064.root must follow the NNC weak law and option B: Root0 OR the existing E_rec, charged once. Realizes construction for all worlds/RZ-STATE and the retained runtime hypotheses are external obligations, not established or used as a filter here. RuntimeCpiReadonlyEntry7 remains PENDING/UNUSED.

## Every specification's route disposition

The no-local-guard test is source-based; a guard-free caller may still need a CLOSED/fission packet for a transitive guard callee. An unresolved emission is a finding, not a native-route waiver. External extraction templates are retained as .lean.txt and never imported as axioms.

| Row | Status | Route | Remaining |
|---|---|---|---|
'''
for r in routes['rows']:s+='| '+r['row']+' | '+r['status']+' | '+r['route']+' | '+r['remaining'].replace('|','/')+' |\n'
(E/'PCM_REMAINING.md').write_text(s)
resource=audit['scope_totals']
h=f'''# PCM supporting Pool library handoff

PARTIAL SUPPORTING WORK ONLY. No Pool row is claimed CLOSED; no parent consumes this output. Security target not established. Required combined import FAILED at prohibited-origin NMK_CompleteFold;47 objects remain quarantined, none copied. Clarification is still pending.

Branch codex/pc-pool-library1-20261110. Only PCM_ files and this evidence directory were changed. Stage commits:34c6adbe0d1 setup,7e4090f919d specification drafts,f5180423761 frozen specifications,d37aeb027c3 slot map,42218007ab1 instance checkpoint; final route/audit commit follows this handoff. No push, shipped source change, key/fund action or ELF rebuild.

Stage1:47 source specifications and61 frozen semantic/spec files, exact Result/error/effect/stop-prefix references and rejection checks; PCM_SPEC_FREEZE.json pins the immutable set. All20 Pool source files checked against b936275465 before the first scope and again at L199. Crates/r1/lock remain4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Source corrections and limits are in PCM_SPEC_DIFFS.md.

Stage2:PCM_MAP.md/json enumerate170 slots:60 MISSING-CHILD-LEMMA,110 OPEN-ROW,0 SPEC-ERROR. Exact supplier roots/statements/domains/caller discharge and representation maps are recorded. LIBB's20 concrete field assignments are acknowledged; they are not reclassified as PCM-gated. Verifier CPI uses NMN_064 plus weak NNC/optionB at the SAME realized execution, never unconditional Root0.

Stage3: six focused compiled groups: Registry,Deployed,TerminalSource,AccountSource,PdaSource,GraphCompositions. Registry.install fills exactly five shared fields; remaining : RSL.PoolLib remains explicit. Source-carrier graph groups are not complete PCM/RSL adapters. Account/Note drafts are excluded. Every gap is listed in PCM_REMAINING.md; no unresolved law or unvalidated packet is promoted.

Stage4:PCM_Top.check compiles with23 named existing split-top bridge fields and unproved assemble; no physical Pool-to-verifier association is claimed. PCM_ROUTES.json records every stage1 row's exact route/finding. Three guard-free boxes emitted with external adapters still pending; full304/319/350 emissions failed at their recorded pinned-tool source sites. Eleven local guard holders require(bn) source fission. Twenty-eight guard-free route checks remain unattempted after the10-extraction budget. Template axioms are text artifacts only.

Gate: PCM_SUPPORT_IMPORT L191 exit0;146 new roots raw ax2 standard-only, no collector disagreement; exact ledger25 optimized binary SHA46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c. Eight fixtures match NMQ exactly. NFX algorithm is byte-identical to NMQ's canonical scan, native L197 exit0 over{scan['modules']} modules, zero dangling/duplicate owners/import mismatches. This is the SUPPORTING closure only. Required headline+NMQ+LIB+NLF+accepted StreamC+PCM import L198 exit1 at NMK_CompleteFold. PCM_AUDIT.json keeps these outcomes separate.

Resources:200/200 Lean/link/audit scopes ({resource['lean_passes']} exit0,{resource['lean_nonzero']} nonzero),10/10 extractions,0 Kani. Scope Lean wall{resource['lean_wall_seconds']:.6f}s; extraction wall{resource['extraction_wall_seconds']:.6f}s; maxRSS{resource['peak_rss_kib']}KiB; swaps0. No timeout,cgroup OOM,cap increase or unchanged memory-failure retry. One interpreter memory threshold stop was replaced by the same optimized native scanner. Every scope has exact target/exit/time/RSS/swaps/revision/source hashes/printed axioms, admission exit0+allowed:true, disk>=40GB and6G/8G/swap0/tasks64 limits. Early Lean-only feature contexts are supplemented without changing original receipts; every extraction has its full resolved crate features and unchanged frozen lock.

L199 retained/import checks rehashed34401 files (8946609768bytes),3036 frozen extraction sources,20 Pool files and61 frozen specification files. L200 final checks pass. One owned scope at a time; host-share/refusal receipts retained. Tools/runner/reservation infrastructure unchanged. All copied imports are hash-pinned, never hardlinked. No entry5 source/object was copied; no foreign cx/pc/pv tree was written.

Pickup: {J(E/'PCM_EXPORT.json')['export']}; PCM_EXPORT.json lists copied own object hashes. SUPPORTING ONLY, full gate blocked. Reuse the owned cache; never delete it or mutate retained exports. PCM_REMAINING.md is the exact resumption queue. Mathematical adapters/observation folds remain Lean work; stopping is budget exhaustion, not Kani exhaustion. Headline remains AspisR1.RPx_Deployed.deployed,frozen3,L154 statement parameter,narrowed D188,100-bit PER-ATTEMPT,privacy,two-transaction design. OptionA transport trust is retained reclassification; RuntimePersistence retained; RuntimeCpiReadonlyEntry7 PENDING/UNUSED.
'''
(E/'PCM_HANDOFF.md').write_text(h)
# Receipt and file hygiene, preserving original receipts and evidence bytes.
for p in E.rglob('__pycache__'):shutil.rmtree(p)
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large,large
for p in E.glob('PCM_*.lean'):assert not re.search(r'^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b|native_decide',p.read_text(),re.M),p
print(json.dumps(dict(status=audit['status'],scopes=200,extractions=10,roots=146,scan_modules=scan['modules'],row_credit=0,oversized_files=0)))
