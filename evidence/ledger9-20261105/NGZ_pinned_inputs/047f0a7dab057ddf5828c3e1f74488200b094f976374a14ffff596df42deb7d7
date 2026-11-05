"""Additional admission checks only, over unchanged historical certificate/ledger gates."""
from pathlib import Path
import json,lzma,re,hashlib,collections,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-s-retarget-20261104'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
p=J(E/'NGF_PROVENANCE.json');receipts={f.parent.name:J(f) for f in E.glob('NGF_L*/receipt.json')};latest={}
for a,r in sorted(receipts.items()):
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=(a,r)
final_modules=[r['target_module'] for r in p['files']]+['NGF_COMBINED_IMPORT','NGF_ProofDriver','NGF_Driver']
for m in final_modules:
 a,r=latest[m];assert (E/a/'sources/NGF_generated'/(m+'.lean')).read_bytes()==(E/(m+'.lean')).read_bytes(),('stale',m)
 assert '-M7000' in r['command'] and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(E/a/'stdout.log').read_text(),re.S):assert {s.strip() for s in match[2].replace('\n',' ').split(',') if s.strip()}<=STD
 for d in re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M):
  if d in latest:assert int(latest[d][0][-3:])<int(a[-3:]),('out-of-order',m,d)
results=[];fixtures=[];metrics=[]
for f in sorted((E/'NGF_audit').glob('*/*.json')):
 x=J(f)
 if 'exit_status' not in x:continue
 assert x['exit_status']==0,str(f)
 parent=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==f.parent.name)
 metrics.append(dict(receipt=str(f.relative_to(E)),parent_attempt=parent,source_revision=receipts[parent]['source_revision'],parent_config_sha256=H((E/(parent+'.json')).read_bytes()),**{k:x[k] for k in ['target','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
 if x['target']=='fixtures':fixtures=x['results'];continue
 if x['target'].startswith('proof'):
  for r in x['results']:
   assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
   g=E/('NGF_NEP_'+x['target']+'_'+r['root']+'_REACHABLE.txt.xz');raw=lzma.decompress(g.read_bytes());assert H(raw)==Path(str(g)[:-3]+'.sha256').read_text().strip()
   results.append(dict(r,mode=x['target'],parent_attempt=parent,source_revision=receipts[parent]['source_revision'],graph_archive=g.name,compressed_sha256=H(g.read_bytes()),uncompressed_sha256=H(raw)))
assert len(fixtures)==8 and len({r['root'] for r in fixtures})==8 and all(r['equal'] for r in fixtures)
assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
manifest=J(E/'NGF_AUDIT_ROOTS.json');names={r['root'] for r in results};assert len(results)==len(names)==len(manifest['roots']) and names==set(manifest['roots'])
scan=[json.loads(l) for l in (E/'NGF_LOADED_scan.jsonl').read_text().splitlines()];assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
mods={r['module'] for r in scan};assert 'RPx_Deployed' in mods and 'NFX_COMBINED_IMPORT' in mods and 'NFY_COMBINED_IMPORT' in mods
assert all(m in mods for m in final_modules if m not in ['NGF_ProofDriver','NGF_Driver'])
assert not ({'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&mods)
summary=dict(status='PASS',modules=len(scan),declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),source_sha256=H((E/'NGF_LOADED_scan.jsonl').read_bytes()),baseline_sha256=H((E/'NGF_EXPECTED_IMPORTS.jsonl').read_bytes()))
(E/'NGF_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')
walker=J(E/'NGF_WALKER_CONFORMANCE.json');assert walker['byte_identical'];assert H((E/'NGF_WALKER_SOURCE.lean').read_bytes())==walker['source_sha256']==H((R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes())
for m in ['NGF_ProofDriver','NGF_Driver']:
 a,r=latest[m];obj=next(v for k,v in r['deps_fingerprint']['selected_objects'].items() if k.endswith('/NFA_WALKER.olean'));assert obj['sha256']==walker['actual_object']['sha256']
proofpin=J(E/next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']=='fixtures')/'NGF_ProofDriver_BINARY_PIN.json')
for a,r in receipts.items():
 if r['kind']=='audit':assert J(E/a/'NGF_ProofDriver_BINARY_PIN.json')==proofpin,('same binary',a)
audit=dict(status='PASS_CANONICAL_CHAIN_B_WITH_HEADLINE',headline=manifest['headline'],combined_import='NGF_COMBINED_IMPORT.lean',combined_source_sha256=H((E/'NGF_COMBINED_IMPORT.lean').read_bytes()),root_count=len(results),results=results,fixtures=fixtures,collect_axioms_disagreements=[r['root'] for r in results if not r['equal']],metrics=metrics,scan=summary,walker_conformance=walker,same_proof_binary=proofpin,scope='Focused cached canonical closure; no cold release claim')
(E/'NGF_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Full theorem-record inventory, independent of graph filtering.
old={t['legacy_name']:t for row in J(P/'NFY_CERTIFICATES.json')['rows'] for t in row['canonical_theorem_associations']};inventory=J(E/'NGF_CERT_INVENTORY.json');gaps=[];certs=[]
for c in inventory:
 refs=[]
 for t in c['theorems']:
  o=old[t['legacy_name']];m=p['module_owner'].get(o['canonical_module'],o['canonical_module']);n=t['canonical_name'];loaded=m in mods
  if loaded:assert n in names,('loaded named certificate declaration lacks raw audit',c['row'],n,m)
  rec=dict(t,canonical_module=m,loaded_and_raw_audited=loaded)
  if not loaded:gaps.append(dict(row=c['row'],legacy_name=t['legacy_name'],canonical_name=n,unloaded_module=m,source=t['source']['path'],chain_B=any(r['source_module']==o['canonical_module'] for r in p['files'])))
  refs.append(rec)
 certs.append(dict(row=c['row'],certificate_sha256=c['certificate_sha256'],records=len(refs),all_named_declarations_loaded=all(t['loaded_and_raw_audited'] for t in refs),theorems=refs))
gaps=list({(g['row'],g['canonical_name'],g['unloaded_module']):g for g in gaps}.values());assert not any(g['chain_B'] for g in gaps)
check=dict(status='PASS_COMPLETE_INVENTORY_WITH_RETAINED_CHAIN_A_GAPS',rows=certs,theorem_record_occurrences=sum(c['records'] for c in certs),distinct_names=len({t['canonical_name'] for c in certs for t in c['theorems']}),gaps=gaps,chain_B_missing=[],not_name_filtered=True)
raw=json.dumps(check,indent=1).encode()+b'\n'
(E/'NGF_CERT_ASSOCIATIONS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NGF_CERT_ASSOCIATIONS.json.sha256').write_text(H(raw)+'\n')
summary_check={k:v for k,v in check.items() if k!='rows'}
summary_check['rows']=[{k:v for k,v in c.items() if k!='theorems'} for c in certs]
summary_check.update(complete_records='NGF_CERT_ASSOCIATIONS.json.xz',uncompressed_sha256=H(raw))
(E/'NGF_CERT_CHECK.json').write_text(json.dumps(summary_check,indent=1)+'\n')
assert J(E/'NGF_REPLAY_NFJ.json')['exit_status']==0 and J(E/'NGF_REPLAY_NFX_LEDGER.json')['exit_status']==0
baseline=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));rows=copy.deepcopy(baseline['rows']);before=J(P/'NFY_LEDGER_DELTA.json');initial={r['row'] for r in before['promotions']}
for r in rows:
 if r['row'] in initial:r['composed_status']='CLOSED'
prior_counts=dict(collections.Counter(r['composed_status'] for r in rows));reviewed={c['row'] for c in inventory};direct={g['row'] for g in gaps};causes={rid:dict(kind='missing_certificate_declaration',gaps=[g for g in gaps if g['row']==rid]) for rid in direct}
for r in rows:
 if r['row'] in reviewed and r['row'] not in direct:r['composed_status']='CLOSED'
while True:
 denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
 for r in rows:
  if r['composed_status']!='CLOSED':continue
  bad=sorted({c for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[]) if c in denied and c not in accepted})
  if bad:r['composed_status']='QUALIFIED';causes[r['row']]=dict(kind='qualified_selected_callee',claims=bad);changed=True
 if not changed:break
assert all(next(r for r in rows if r['row']==rid)['composed_status']=='CLOSED' for rid in initial)
promotions=[];remaining=[]
for r in rows:
 if r['row'] not in reviewed:continue
 if r['composed_status']!='CLOSED':remaining.append(dict(row=r['row'],function=r['function'],reason=causes[r['row']]))
 elif r['row'] not in initial:promotions.append(dict(row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],before='QUALIFIED',after='CLOSED',canonical_import='NGF_COMBINED_IMPORT',audit='NGF_AUDIT.json',coherence='NGF_SCAN.json',certificate_check='NGF_CERT_CHECK.json',native_evidence='Historical source validator and certificates replayed unchanged; no new Kani pass',transport='P6/D188 option A retained; namespace/import retarget only'))
claim_rows={}
for row in rows:
 if row['composed_status']!='CLOSED':
  for claim in row['selected_claims']:claim_rows.setdefault(claim,[]).append(row['row'])
def missing_names(rid,seen=None):
 seen=set() if seen is None else seen
 if rid in seen:return set()
 seen.add(rid);cause=causes.get(rid,{})
 out={g['canonical_name'] for g in cause.get('gaps',[])}
 for claim in cause.get('claims',[]):
  for child in claim_rows.get(claim,[]):out.update(missing_names(child,seen))
 return out
for item in remaining:
 item['transitive_missing_declarations']=sorted(missing_names(item['row']))
 item['missing_chain_B_declarations']=[]
 assert item['transitive_missing_declarations'],('unresolved qualification explanation',item['row'])
spec=J(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];counts=lambda rs:dict(collections.Counter(r['composed_status'] for r in rs))
# (ag) 599-row inventory: all 12 additions remain OPEN. No fabricated credit
# to independent concurrent jobs; their deltas compose separately.
overlay=J(E.parent/'inv-repair-20261104/NGB_LEDGER_DELTA.json');assert len(overlay['new_rows'])==12 and all(r['status']=='OPEN' for r in overlay['new_rows']) and not overlay['removed_rows']
repaired_before=dict(prior_counts);repaired_before['OPEN']+=12;after=counts(rows);after['OPEN']+=12
delta=dict(status='PASS',baseline='NFY_LEDGER_DELTA plus NGB 599-row overlay',baseline_sha256=H((P/'NFY_LEDGER_DELTA.json').read_bytes()),NGB_overlay_sha256=H((E.parent/'inv-repair-20261104/NGB_LEDGER_DELTA.json').read_bytes()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),promotions=promotions,remaining_qualified_S=remaining,before=repaired_before,after=after,legacy_587_after=counts(rows),S_after=counts([r for r in rows if r['function'] in spec['functions']]),S_roots=[dict(function=f,rows=[r['row'] for r in rows if r['function']==f],status='CLOSED' if all(r['composed_status']=='CLOSED' for r in rows if r['function']==f) else 'QUALIFIED') for f in spec['roots']],reviewed_S_rows=sorted(reviewed),prior_NFY_promotions_retained=sorted(initial),chain_A_delta_not_imported=True,inventory_rows=599,inventory_identity_unchanged=True,new_trust_rows=[],removed_trust_rows=[],security_target_established=False,cold_release_replay=False)
from NGF_checks import check_bundle,check_delta
assert check_bundle(audit,scan,manifest) and check_delta(baseline,before,delta,check,inventory,scan,p)
(E/'NGF_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
lines=['# Remaining qualified slice S rows','',f"NGF restores {len(promotions)} rows beyond NFY. Slice S: {delta['S_after']}. No chain-B declaration remains missing. Remaining members require chain A and selected-callee propagation, not Kani or extraction.",'','| Row | Member | Exact missing declaration or denied selected callee |','|---|---|---|']
for r in remaining:
 cause=r['reason'];detail='; '.join(r['transitive_missing_declarations']);detail+=(' (selected callees: '+ '; '.join(cause['claims'])+')') if cause.get('claims') else '';lines.append(f"| {r['row']} | {r['function']} | {detail} |")
(E/'NGF_REMAINING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(roots=len(results),scan=summary,promotions=len(promotions),after=after,S=delta['S_after'])))
