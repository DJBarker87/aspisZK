from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
ats=[json.loads(l) for l in (E/'PCA_ATTEMPTS.jsonl').read_text().splitlines()]
formal=[r for r in ats if r['attempt'].startswith('PCA_L')];native=[r for r in ats if r['attempt'].startswith('PCA_K')]
assert len(formal)==60 and len(native)<=90
allowed={'propext','Classical.choice','Quot.sound'}
def output(a):return lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
def results(a):return [json.loads(l[len('NEP_RESULT '):]) for l in output(a).splitlines() if l.startswith('NEP_RESULT ')]
raw=results('PCA_L059');assert len(raw)==47 and all(r['equal'] and set(r['walked_axioms'])<=allowed for r in raw)
fx=results('PCA_L058');assert len(fx)==8 and all(r['equal'] for r in fx)
assert [r['walked_axioms'] for r in fx]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
loads=[json.loads(l) for l in lzma.decompress((E/'PCA_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(not r['dangling'] and r['imports_match'] for r in loads)
binaries=[json.loads((E/('PCA_binary_'+m+'.json')).read_text()) for m in ['fixtures','proof0','scan']]
assert all(x['unchanged'] and x['exit']==0 for x in binaries) and len({x['before'] for x in binaries})==1
current=json.loads((E/'PCA_CURRENT_SOURCE_CHECK.json').read_text());assert all(sha((E/(r['module']+'.lean')).read_bytes())==r['source_sha256'] for r in current)
assert all(int(r['swaps'])==0 for r in ats)
for r in native:
 a=r['attempt'];g=E/(a+'-graph-check.json');l=E/(a+'-lock-check.json')
 data={'host_receipt_sha256':sha((E/a/'receipt.json').read_bytes()),'host_receipt':r,'proof_credit':False,'classification':'compiler/preflight/codegen attempt; no matched native proof/control pair','resolved_features_every_crate':None}
 if g.exists():
  graph=json.loads(g.read_text());assert graph['graph_matches_frozen'];data['resolved_features_every_crate']=graph['resolved_features_every_crate'];data['graph']=graph
 if l.exists():
  lock=json.loads(l.read_text());assert lock['unchanged'];data['lock']=lock
 elif a=='PCA_K002':data['lock_recovery']=json.loads((E/'PCA_K002_RECOVERY.json').read_text())
 else:data['lock_status']='No Kani launch: metadata preflight rejected before native command'
 data['diagnostics']=[s for s in output(a).splitlines() if s.startswith('error') or 'panicked at' in s or 'Arbitrary' in s or 'failed to spawn' in s]
 (E/(a+'_DEPLOYED_RECEIPT.json')).write_text(json.dumps(data,indent=1)+'\n')
audit={
 'status':'FOCUSED_INTERMEDIATE_GATE_PASS_OWNER_OPEN',
 'headline':'AspisR1.RPx_Deployed.deployed','model':'frozen3','L154':'statement parameter','D188':'narrowed; no change',
 'cohort_slots':{'digest':'op43','error':'op44','PDA':'op38 quantified'},
 'scope':'36 current compiled PCA model/interface/support modules; 47 raw roots; no POOL:328 root',
 'source_check':current,'combined_import_receipt':'PCA_L055','raw_receipt':'PCA_L059','scan_receipt':'PCA_L060','fixtures_receipt':'PCA_L058',
 'raw_roots':raw,'standard_axioms_only':True,'raw_equals_collect_axioms':True,'fixtures':fx,'same_fixture_raw_scan_binary':binaries,
 'scan':{'exit':0,'loaded_modules':len(loads),'declarations':sum(r['declarations'] for r in loads),'references':sum(r['edges'] for r in loads),'dangling':0,'import_mismatches':0},
 'budget':{'kani_native_scopes_used':len(native),'kani_native_limit':90,'formal_scopes_used':60,'formal_limit':60,'extraction_used':0,'extraction_limit':0},
 'formal_stage_scopes':{'stage1_draft':5,'stage2_support_interfaces_and_failed_fold':49,'focused_gate':6},
 'native_semantic_proofs':0,'matched_native_failing_controls':0,'pool_rows_closed':0,'root_emitted':False,'security_target_established':False,
 'max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in ats),'max_scope_memory_peak_bytes':max(int(r['cgroup_memory_peak_bytes']) for r in ats),'swap':0,
 'remaining':['fixed full-Result owner specification including ProgramError payload/native-view domain','exact RowSpecs and complete Result/event/state source fold','global live-token and release proof','both CPI native bridges and controls','transcription/native association','pending CPI account-view frame and distinct SDK/ABI frames'],
 'E7_note':'PASS for retained intermediates only. E1-E6 are NOT MET. The raw/kernel audit does not establish source faithfulness, a child packet, native association or owner closure.',
 'native_note':'Actual per-attempt commands, deployed features for every resolved crate, strict frozen-lock graph check and post-lock/recovery evidence are in PCA_Kxxx_DEPLOYED_RECEIPT.json. Compiler/preflight success is never a semantic pass.',
 'elfs':{'reproduced':False,'reason':'No shipped repository source change; scratch-only harness patches','default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'}
}
(E/'PCA_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Explicit per-child cost evidence, without fabricating unmeasured native costs.
children=json.loads((E/'PCA_CHILDREN.json').read_text())['direct_pool_children']
s='# PCA per-child remaining cost evidence\n\nNo child is CLOSED here. Timings below are interface elaboration, not closure or native proof cost. No defensible end-to-end per-child cost range was measured. Each unknown is retained.\n\n| Child | Class / owner | Observed cost | Exact remaining work |\n|---|---|---|---|\n'
for c in children:
 n=int(c['row'].split(':')[1]);m=f'PCA_RowSpec_POOL_{n}';rs=[r for r in formal if r['module']==m and r['exit_status']==0];cost=f"{rs[-1]['wall_seconds']:.3f}s last interface compile; native unmeasured" if rs else 'No typed module or native result'
 if c['class']=='A':need='PCB concrete packet/merge/gate, SAME-argument representation/domain/frame lift; proof not duplicated'
 elif n==332:need='Unrestricted native input/source-header association, full error/word representation, native contract and control/fidelity; see native attempts'
 elif n in [364,365,367]:need='Exact argument/native-view and enum association, native controls; uniqueness additionally one-iteration source loop plus Lean induction'
 elif n==356:need='Full deployed forwarding packet, SDK invocation/borrow checks to syscall, exact Result/frames and native control'
 else:need='Exact concrete reference/domain/Result/effects/frame/abort packet, child instantiations, then native cut/control; cost unmeasured'
 s+=f"| {c['row']} | {c['class']} / {c['owner']} | {cost} | {need} |\n"
s+='\nNested POOL:357 (class D): complete invoke_signed forwarding/SDK packet, exact seed groups/bytes/infos/reply/frames and controls are unmeasured and OPEN. Pending runtime candidate clauses are not included in a numerical proof-cost estimate.\n'
(E/'PCA_CHILD_COSTS.md').write_text(s)
print('Summary regenerated: focused gate PASS, '+str(len(native))+'/90 native scopes, 60/60 formal, zero Pool closures; per-child unknown costs retained.')
