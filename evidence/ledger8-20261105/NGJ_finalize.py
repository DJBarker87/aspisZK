from pathlib import Path
import json,lzma,hashlib,re,collections
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
receipts={p.parent.name:J(p) for p in E.glob('NGJ_L*/receipt.json')};assert len(receipts)==40
for a,r in receipts.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
 if r['kind']=='lean':assert '-M7000' in r['command']
 if r['kind']=='link':assert '-O3' in r['command']
 if a not in ['NGJ_L001','NGJ_L002','NGJ_L009','NGJ_L027','NGJ_L028','NGJ_L029','NGJ_L037']:assert r['exit_status']==0,(a,r['exit_status'])
 for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(E/a/'stdout.log').read_text() if r['kind']=='lean' else '',re.S):assert {re.sub(r'\.\{[^}]*\}','',x.strip()) for x in m[2].replace('\n',' ').split(',') if x.strip()}<=STD

def scan(path):
 expected={r['module']:r['imports'] for r in map(json.loads,(E/'NGJ_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};rows=[json.loads(l) for l in path.read_text().splitlines()];bad=[r for r in rows if r['dangling'] or r['duplicate_owners'] or not r['imports_match']]
 return dict(status='PASS' if not bad else 'FAIL',modules=len(rows),declarations=sum(r['declarations'] for r in rows),edges=sum(r['edges'] for r in rows),dangling=sum(len(r['dangling']) for r in rows),incompatible_owners=sum(len(r['duplicate_owners']) for r in rows),import_mismatches=sum(not r['imports_match'] for r in rows),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in rows),missing_expected_import_baselines=sum(not r['imports_match'] and r['module'] not in expected for r in rows),different_expected_import_lists=sum(not r['imports_match'] and r['module'] in expected for r in rows),defects=bad,sha256=H(path.read_bytes())),rows
v,vr=scan(E/'NGJ_LOADED_scan.jsonl');p,pr=scan(E/'NGJ_POOL_LOADED_scan.jsonl');assert v['status']=='PASS'
needed={'NGI_COMBINED_IMPORT','NFX_COMBINED_IMPORT','NFS_COMBINED_IMPORT','NFT_STAGE2_IMPORT','NFU_STAGE2_IMPORT','RPx_Deployed','NGJ_VERIFIER_IMPORT'};assert needed<={r['module'] for r in vr};v['required_roots_loaded']=sorted(needed)
summary=dict(verifier=v,pool=p,full_all_slices=dict(status='FAILED_IMPORT',attempt='NGJ_L002',reason='Original/canonical SDK GuardBody declaration collision'),scope='No all-slices coherence pass claimed; verifier and historical Pool scans have distinct selected environments')
(E/'NGJ_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')

def audit(modes,manifest,fixture_mode,binary):
 results=[];metrics=[]
 for mode in modes:
  files=list((E/'NGJ_audit'/mode).glob('*.json'));assert len(files)==1,(mode,files);x=J(files[0]);assert x['exit_status']==0,mode
  parent=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==mode)
  metrics.append(dict(parent=parent,**{k:x[k] for k in ['target','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
  for t in x['results']:
   assert set(t['walked_axioms'])<=STD and set(t['collect_axioms'])<=STD
   name='NGJ_NEP_'+x['target']+'_'+t['root']+'_REACHABLE.txt';q=E/(name+'.xz');raw=lzma.decompress(q.read_bytes());assert H(raw)==(E/(name+'.sha256')).read_text().strip()
   results.append(dict(t,attempt=parent,raw_graph=q.name,raw_graph_sha256=H(raw),archive_sha256=H(q.read_bytes())))
 expected=J(E/manifest)['roots'];assert len(results)==len(expected)==len({r['root'] for r in results}) and {r['root'] for r in results}==set(expected)
 fx=J(next((E/'NGJ_audit'/fixture_mode).glob('*.json')));assert fx['exit_status']==0 and len(fx['results'])==8 and all(x['equal'] for x in fx['results']);assert all(x['walked_axioms'] for x in fx['results'][:4]) and all(not x['walked_axioms'] for x in fx['results'][4:])
 parent=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==fixture_mode);bp=J(E/parent/(binary+'_BINARY_PIN.json'))
 for m in modes:
  a=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==m);assert J(E/a/(binary+'_BINARY_PIN.json'))==bp
 return dict(root_count=len(results),results=results,fixtures=fx['results'],same_proof_binary=bp,collect_axioms_disagreements=[x['root'] for x in results if not x['equal']],metrics=metrics)
auditv=audit(['batch'+str(i) for i in range(16)],'NGJ_AUDIT_ROOTS.json','fixtures','NGJ_ProofDriver');auditp=audit(['poolroots'],'NGJ_POOL_ROOTS.json','poolfixtures','NGJ_PoolProofDriver')
walker=J(E/'NGJ_WALKER_CONFORMANCE.json');assert walker['byte_identical'] and H((E/'NGJ_WALKER_SOURCE.lean.txt').read_bytes())==walker['source_sha256']
for a,r in receipts.items():
 if r['kind']=='audit':
  objs=r['deps_fingerprint']['selected_objects'];actual=next(o for p,o in objs.items() if p.endswith('/NFA_WALKER.olean'));assert actual['sha256']==walker['actual_object']['sha256']
auditv.update(full_all_slices_status='FAILED_OWNER_CONFLICT',verifier_status='PASS',headline='AspisR1.RPx_Deployed.deployed',walker_conformance=walker,pool_diagnostic=auditp,scan='NGJ_SCAN.json',no_new_theorem=True,cold_release_replay=False)
(E/'NGJ_AUDIT.json').write_text(json.dumps(auditv,indent=1)+'\n')

def path(rows,root,target):
 g={r['module']:r['imports'] for r in rows};seen={root:[root]};q=collections.deque([root])
 while q:
  n=q.popleft()
  for c in g.get(n,[]):
   if c not in seen:seen[c]=seen[n]+[c];q.append(c)
 return seen.get(target)
conflicts=[]
for a,old,new,name in [('NGJ_L027','S2SdkOwnedGuardBodyV1','RPz7_S2SdkOwnedGuardBodyV1','AspisS2OwnedStage1.SdkReference.GuardBody.tacticSdk_finish_guard_write'),('NGJ_L028','PreparedFromQmSourceBridge','RPz7_PreparedFromQmSourceBridge','AspisR1PublicPreparation.PreparedFromQmSourceBridge.PrepQM'),('NGJ_L029','S1SemanticPhaseV1','AspisR1PublicPreparation.Types','AspisR1PublicPreparation.verifier.Phase')]:
 text=(E/a/'stdout.log').read_text();assert name in text
 pins={p:o for p,o in receipts[a]['deps_fingerprint']['selected_objects'].items() if p.endswith('/'+old.replace('.','/')+'.olean') or p.endswith('/'+new.replace('.','/')+'.olean')}
 conflicts.append(dict(declaration=name,original_owner=old,canonical_owner=new,attempt=a,verifier_import_path=path(vr,'NGJ_VERIFIER_IMPORT',new),Pool_import_path=path(pr,'NGJ_POOL_LEGACY_IMPORT',old),minimal_pair_object_pins=pins,qualifies_verifier_rows=[],affected_scope='Pool plus deployed/coherent verifier joint forest; no admitted Pool consumer row exists in the 599-row inventory',disposition='REJECT joint import; no slice edits or owner renaming'))
(E/'NGJ_CONFLICTS.json').write_text(json.dumps(dict(full_attempt='NGJ_L002',conflicts=conflicts,Pool_legacy_dangling=p['dangling'],retained_verifier_rows_qualified=[],reason='Verifier-only forest independently passes scan and raw audit; Pool association already OPEN outside row basis; no failed joint claim is promoted'),indent=1)+'\n')
metrics=dict(charged_slots=40,by_kind=dict(collections.Counter(r['kind'] for r in receipts.values())),successful=sum(r['exit_status']==0 for r in receipts.values()),failures={a:r['exit_status'] for a,r in receipts.items() if r['exit_status']},scope_wall_sum_seconds=sum(r['wall_seconds'] for r in receipts.values()),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts.values()),swaps=0,Kani=0,extraction=0,new_theorems=0,caps='MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean -M7000',timeouts=0,memory_kills=0)
(E/'NGJ_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
print(json.dumps(dict(verifier_roots=len(auditv['results']),Pool_roots=len(auditp['results']),verifier_scan={k:v[k] for k in ['modules','dangling','incompatible_owners','import_mismatches']},Pool_scan={k:p[k] for k in ['modules','dangling','incompatible_owners','import_mismatches']},metrics=metrics)))
