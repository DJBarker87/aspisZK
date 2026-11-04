"""Additional admission checks only, over unchanged historical certificate/ledger gates."""
from pathlib import Path
import json,lzma,re,hashlib,collections,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-s-retarget-20261104'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
p={'files':[]};receipts={f.parent.name:J(f) for f in E.glob('NGI_L*/receipt.json')};latest={}
for a,r in sorted(receipts.items()):
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=(a,r)
final_modules=[r['target_module'] for r in p['files']]+['NGI_COMBINED_IMPORT','NGI_ProofDriver','NGI_Driver']
for m in final_modules:
 a,r=latest[m];assert (E/a/'sources/NGI_generated'/(m+'.lean')).read_bytes()==(E/(m+'.lean')).read_bytes(),('stale',m)
 assert '-M7000' in r['command'] and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(E/a/'stdout.log').read_text(),re.S):assert {re.sub(r'\.\{[^}]*\}', '', s.strip()) for s in match[2].replace('\n',' ').split(',') if s.strip()}<=STD
 for d in re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M):
  if d in latest:assert int(latest[d][0][-3:])<int(a[-3:]),('out-of-order',m,d)
results=[];fixtures=[];metrics=[]
for f in sorted((E/'NGI_audit').glob('*/*.json')):
 x=J(f)
 if 'exit_status' not in x:continue
 assert x['exit_status']==0,str(f)
 parent=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==f.parent.name)
 metrics.append(dict(receipt=str(f.relative_to(E)),parent_attempt=parent,source_revision=receipts[parent]['source_revision'],parent_config_sha256=H((E/(parent+'.json')).read_bytes()),**{k:x[k] for k in ['target','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
 if x['target']=='fixtures':fixtures=x['results'];continue
 if x['target'].startswith('proof'):
  for r in x['results']:
   assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
   g=E/('NGI_NEP_'+x['target']+'_'+r['root']+'_REACHABLE.txt.xz');raw=lzma.decompress(g.read_bytes());assert H(raw)==Path(str(g)[:-3]+'.sha256').read_text().strip()
   results.append(dict(r,mode=x['target'],parent_attempt=parent,source_revision=receipts[parent]['source_revision'],graph_archive=g.name,compressed_sha256=H(g.read_bytes()),uncompressed_sha256=H(raw)))
assert len(fixtures)==8 and len({r['root'] for r in fixtures})==8 and all(r['equal'] for r in fixtures)
assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
manifest=J(E/'NGI_AUDIT_ROOTS.json');names={r['root'] for r in results};assert len(results)==len(names)==len(manifest['roots']) and names==set(manifest['roots'])
scan=[json.loads(l) for l in (E/'NGI_LOADED_scan.jsonl').read_text().splitlines()];assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
mods={r['module'] for r in scan};assert 'RPx_Deployed' in mods and 'NFX_COMBINED_IMPORT' in mods and 'NFY_COMBINED_IMPORT' in mods
assert all(m in mods for m in final_modules if m not in ['NGI_ProofDriver','NGI_Driver'])
assert not ({'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&mods)
summary=dict(status='PASS',modules=len(scan),declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),source_sha256=H((E/'NGI_LOADED_scan.jsonl').read_bytes()),baseline_sha256=H((E/'NGI_EXPECTED_IMPORTS.jsonl').read_bytes()))
(E/'NGI_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')
walker=J(E/'NGI_WALKER_CONFORMANCE.json');assert walker['byte_identical'];assert H((E/'NGI_WALKER_SOURCE.lean').read_bytes())==walker['source_sha256']==H((R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes())
for m in ['NGI_ProofDriver','NGI_Driver']:
 a,r=latest[m];obj=next(v for k,v in r['deps_fingerprint']['selected_objects'].items() if k.endswith('/NFA_WALKER.olean'));assert obj['sha256']==walker['actual_object']['sha256']
proofpin=J(E/next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']=='fixtures')/'NGI_ProofDriver_BINARY_PIN.json')
for a,r in receipts.items():
 if r['kind']=='audit':assert J(E/a/'NGI_ProofDriver_BINARY_PIN.json')==proofpin,('same binary',a)
audit=dict(status='PASS_BOTH_CHAINS_WITH_HEADLINE',headline=manifest['headline'],combined_import='NGI_COMBINED_IMPORT.lean',combined_source_sha256=H((E/'NGI_COMBINED_IMPORT.lean').read_bytes()),root_count=len(results),results=results,fixtures=fixtures,collect_axioms_disagreements=[r['root'] for r in results if not r['equal']],metrics=metrics,scan=summary,walker_conformance=walker,same_proof_binary=proofpin,scope='Focused cached canonical closure; no cold release claim')
(E/'NGI_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Inventory queried from the actual kernel-loaded combined environment.
inventory=json.loads(lzma.decompress((E/'NGI_CERT_INVENTORY.json.xz').read_bytes()))
entries={};modules=None
for f in sorted(E.glob('NGI_L*/stdout.log')):
 for line in f.read_text().splitlines():
  if 'NGI_CERT_MODULES ' in line:
   ms=json.loads(line.split('NGI_CERT_MODULES ',1)[1]);assert modules is None or modules==ms;modules=ms
  if 'NGI_CERT_ENTRY ' in line:
   t=json.loads(line.split('NGI_CERT_ENTRY ',1)[1]);assert t['name'] not in entries;entries[t['name']]=t
assert len(entries)==261 and modules
records=[];gaps=[]
for row in inventory:
 refs=[]
 for t in row['theorems']:
  e=entries[t['canonical_name']];actual=modules[e['module_idx']] if e['found'] and e['module_idx'] is not None else None
  good=e['found'] and actual==t['canonical_module'] and t['canonical_name'] in names
  if not good:gaps.append(dict(row=row['row'],name=t['canonical_name'],expected_owner=t['canonical_module'],actual_owner=actual,found=e['found'],raw_audited=t['canonical_name'] in names))
  refs.append(dict(t,found=e['found'],actual_owner=actual,loaded_and_raw_audited=good,kernel_type_sha256=H(e.get('type','').encode())))
 records.append(dict(row=row['row'],function=row['function'],certificate_sha256=row['certificate_sha256'],records=len(refs),all_named_declarations_loaded=all(t['loaded_and_raw_audited'] for t in refs),theorems=refs))
assert len(records)==97
raw=json.dumps(records,indent=1).encode()+b'\n';(E/'NGI_CERT_ASSOCIATIONS.json.xz').write_bytes(lzma.compress(raw));(E/'NGI_CERT_ASSOCIATIONS.json.sha256').write_text(H(raw)+'\n')
(E/'NGI_DECLARATION_INVENTORY.json').write_text(json.dumps(dict(modules=modules,entries=entries),indent=1)+'\n')
check=dict(status='PASS' if not gaps else 'FINDING',rows=[{k:v for k,v in r.items() if k!='theorems'} for r in records],all_S_occurrences=97,selected_certificates=97,theorem_record_occurrences=sum(r['records'] for r in records),distinct_names=len(entries),missing_or_wrong_owner=gaps,not_name_filtered=True,complete_records='NGI_CERT_ASSOCIATIONS.json.xz',uncompressed_sha256=H(raw),zero_named_records=[r['row'] for r in records if not r['records']],zero_record_explanation='Selected historical WideExact::to_limbs row contains no named Lean theorem records; historical native admission retained, no fabricated theorem association.')
(E/'NGI_CERT_CHECK.json').write_text(json.dumps(check,indent=1)+'\n')
assert not gaps,('certificate inventory failure',gaps)
assert J(E/'NGI_REPLAY_NFX_LEDGER.json')['exit_status']==0
# Additive NGB overlay is unchanged; all twelve additional rows remain OPEN.
baseline=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));rows=copy.deepcopy(baseline['rows']);original={r['row']:copy.deepcopy(r) for r in rows}
prior=J(E.parent/'slice-s-retarget2-20261104/NGE_LEDGER_DELTA.json');nfy=J(P/'NFY_LEDGER_DELTA.json')
reviewed={r['row'] for r in records};denied_direct={r['row'] for r in records if not r['all_named_declarations_loaded']}
prior_promoted={r['row'] for r in nfy['promotions']}|{r['row'] for r in prior['promotions']}
for r in rows:
 if r['row'] in prior_promoted:r['composed_status']='CLOSED'
counts=lambda rs:dict(collections.Counter(r['composed_status'] for r in rs))
before=counts(rows);before['OPEN']+=12
for r in rows:
 if r['row'] in reviewed and r['row'] not in denied_direct:r['composed_status']='CLOSED'
# Preserve the selected-callee denial propagation from predecessor checks.
def propagate(rs):
 while True:
  denied={c for r in rs if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rs if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
  for r in rs:
   if r['composed_status']=='CLOSED' and any(c in denied and c not in accepted for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[])):
    r['composed_status']='QUALIFIED';changed=True
  if not changed:return
propagate(rows)
overlay=J(E.parent/'inv-repair-20261104/NGB_LEDGER_DELTA.json');assert len(overlay['new_rows'])==12 and all(r['status']=='OPEN' for r in overlay['new_rows']) and not overlay['removed_rows']
spec=J(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];srows=[r for r in rows if r['function'] in spec['functions']];assert len(srows)==97
remaining=[dict(row=r['row'],function=r['function'],missing_declarations=[g for g in gaps if g['row']==r['row']]) for r in srows if r['composed_status']!='CLOSED']
promotions=[dict(row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],before='QUALIFIED',after='CLOSED',canonical_import='NGI_COMBINED_IMPORT',certificate_check='NGI_CERT_CHECK.json',audit='NGI_AUDIT.json',scan='NGI_SCAN.json') for r in srows if r['composed_status']=='CLOSED' and original[r['row']]['composed_status']!='CLOSED' and r['row'] not in prior_promoted]
after=counts(rows);after['OPEN']+=12
roots=[dict(function=f,rows=[r['row'] for r in srows if r['function']==f],status='CLOSED' if all(r['composed_status']=='CLOSED' for r in srows if r['function']==f) else 'QUALIFIED') for f in spec['roots']]
delta=dict(status='PASS',baseline='NFX + NFY + NGE scoped S credit with unchanged NGB 599-row additive overlay; NGF credited through combined checks, not by status union',baseline_sha256=H((E.parent/'slice-s-retarget2-20261104/NGE_LEDGER_DELTA.json').read_bytes()),NGB_overlay_sha256=H((E.parent/'inv-repair-20261104/NGB_LEDGER_DELTA.json').read_bytes()),inventory_rows=599,inventory_identity_unchanged=True,historical_NFX_rows=587,before=before,after=after,S_before=prior['S_after'],S_after=counts(srows),S_roots=roots,S_roots_CLOSED=sum(r['status']=='CLOSED' for r in roots),promotions=promotions,remaining_qualified_S=remaining,selected_callee_denial_propagation=True,all_named_records_checked=True,new_trust_rows=[],removed_trust_rows=[],security_target_established=False,cold_release_replay=False,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),concurrent_D_Pool_deltas='Separate; no unimported concurrent credit inferred')
assert all(r['composed_status']=='CLOSED' for r in srows) and len(promotions)==14 and delta['S_roots_CLOSED']==7
(E/'NGI_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
(E/'NGI_REMAINING.md').write_text('''# Remaining obligations\n\nSlice S: 97/97 occurrences CLOSED, 7/7 roots CLOSED under the retained trust inventory. No S row remains QUALIFIED; no named declaration is missing and no selected-callee denial remains.\n\nNo new proof, Kani or extraction obligation remains for this join. D/Pool joins, L159/L181, the coherent cold release replay L187 and final trust/source/artifact audit L188 remain outside this job. These cached-cohort results do not establish the overall 100-bit per-attempt security target.\n''')
print(json.dumps(dict(roots=len(results),scan=summary,certificate_records=check['theorem_record_occurrences'],certificate_names=len(entries),new_rows=len(promotions),S=delta['S_after'],S_roots=delta['S_roots_CLOSED'])))
