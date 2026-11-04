"""Assemble measured gates and an additive S-only ledger delta."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,collections,sys
sys.dont_write_bytecode=True
from NGE_checks import check_bundle,check_delta,derive,STD
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-retarget-20261104';R=E.parents[1]
J=lambda p:json.loads(p.read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventory=J(E/'NGE_DECLARATION_INVENTORY.json');assert inventory['status']=='PASS' and not inventory['incompatible_owners']
prov=J(E/'NGE_PROVENANCE.json');manifest=J(E/'NGE_AUDIT_ROOTS.json');certs=J(E/'NGE_CERTIFICATES.json')
receipts={f.parent.name:J(f) for f in E.glob('NGE_L*/receipt.json')};latest={}
for a,r in sorted(receipts.items()):
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=(a,r)
for m in ['NGE_'+n for n in prov['order']]+['NGE_COMBINED_IMPORT','NGE_ProofDriver','NGE_Driver']:
 a,r=latest[m];assert (E/a/'sources/NGE_generated'/(m+'.lean')).read_bytes()==(E/(m+'.lean')).read_bytes(),('stale source',m)
 assert '-M7000' in r['command']
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(E/a/'stdout.log').read_text(),re.S):assert {s.strip() for s in match[2].replace('\n',' ').split(',') if s.strip()}<=STD,(m,match[1])
 for d in re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M):
  if d.startswith('NGE_') and d in latest:assert int(latest[d][0][-3:])<int(a[-3:]),('stale ordering',m,d)
results=[];fixtures=[];metrics=[];binary=[]
for f in sorted((E/'NGE_audit').glob('*/*.json')):
 x=J(f)
 if 'exit_status' not in x:continue
 assert x['exit_status']==0,(f,x['exit_status'])
 parent=next(a for a,r in receipts.items() if r['kind']=='audit' and r['module']==f.parent.name);rr=receipts[parent]
 metrics.append(dict(parent_attempt=parent,receipt=str(f.relative_to(E)),source_revision=rr['source_revision'],parent_config_sha256=H(E/(parent+'.json')),**{k:x[k] for k in ['target','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
 if x['target']=='fixtures' or x['target'].startswith('proof'):binary.append(J(E/parent/'NGE_ProofDriver_BINARY_PIN.json')['sha256'])
 if x['target']=='fixtures':fixtures=x['results']
 if x['target'].startswith('proof'):
  for r in x['results']:
   graph=E/('NGE_NEP_'+x['target']+'_'+r['root']+'_REACHABLE.txt.xz');raw=lzma.decompress(graph.read_bytes());h=hashlib.sha256(raw).hexdigest();assert h==Path(str(graph)[:-3]+'.sha256').read_text().strip()
   results.append(dict(r,mode=x['target'],parent_attempt=parent,source_revision=rr['source_revision'],graph_archive=graph.name,compressed_sha256=H(graph),uncompressed_sha256=h))
scan=[json.loads(l) for l in (E/'NGE_LOADED_scan.jsonl').read_text().splitlines()]
summary=dict(status='PASS',modules=len(scan),declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),source_sha256=H(E/'NGE_LOADED_scan.jsonl'),baseline_sha256=H(E/'NGE_EXPECTED_IMPORTS.jsonl'))
# Both driver prefixes and full walker bytes are fixed, selector/runtime paths only.
walk=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();conformance=dict(byte_identical=True,walker_source_sha256=hashlib.sha256(walk).hexdigest(),resolved_module='NFA_WALKER',source='evidence/axaudit2-20261102/NEP_WALKER.lean',driver_diffs=['NGE_ProofDriver.diff','NGE_Driver.diff'],inherited=J(P/'NFY_WALKER_CONFORMANCE.json'))
for name in ['Driver','ProofDriver']:
 a=(P/('NFY_'+name+'.lean')).read_text();b=(E/('NGE_'+name+'.lean')).read_text();expected=a.replace('NFY_COMBINED_IMPORT','NGE_COMBINED_IMPORT').replace('NFY_AUDIT_ROOTS','NGE_AUDIT_ROOTS').replace('NFY_EXPECTED_IMPORTS','NGE_EXPECTED_IMPORTS').replace('NFY_LOADED_scan','NGE_LOADED_scan');assert b==expected,('unadmitted driver change',name)
# All chosen walker sidecars must match the admitted parent's selected bytes.
parent_pins=J(P/'NFY_L105/receipt.json')['deps_fingerprint']['selected_objects']
expected={str(Path(k).name):v['sha256'] for k,v in parent_pins.items() if '/NFA_WALKER.' in k}
for a,r in receipts.items():
 if r['kind'] not in ['lean','audit']:continue
 for k,v in r.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if Path(k).name in expected:assert v['sha256']==expected[Path(k).name],('walker object mismatch',a,k)
conformance['admitted_walker_objects']=expected
(E/'NGE_WALKER_CONFORMANCE.json').write_text(json.dumps(conformance,indent=1)+'\n')
audit=dict(status='PASS_COHERENT_CHAIN_A_WITH_HEADLINE',headline=manifest['headline'],combined_import='NGE_COMBINED_IMPORT.lean',combined_source_sha256=H(E/'NGE_COMBINED_IMPORT.lean'),root_count=len(results),results=results,fixtures=fixtures,collect_axioms_disagreements=[r['root'] for r in results if not r['equal']],metrics=metrics,scan=summary,proof_driver_binary_sha256=binary,walker_conformance=conformance,scope='Focused cached closure, not cold release replay')
assert check_bundle(audit,scan,manifest,certs,prov)
(E/'NGE_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'NGE_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')
assert J(E/'NGE_REPLAY_NFX_LEDGER.json')['exit_status']==0
base=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));prior=J(P/'NFY_LEDGER_DELTA.json');rows,gaps,causes=derive(base,certs,{r['module'] for r in scan});by={r['row']:r for r in rows};old_closed={r['row'] for r in prior['promotions']};reviewed={r['row'] for r in certs['rows']}
promotions=[dict(row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],before='QUALIFIED',after='CLOSED',canonical_import='NGE_COMBINED_IMPORT',audit='NGE_AUDIT.json',coherence='NGE_SCAN.json',certificate_inventory='NGE_CERT_CHECK.json',native_evidence='Historical certificate retained, no new native pass',transport='P6/D188 option A retained/reclassified') for r in rows if r['row'] in reviewed-old_closed and r['composed_status']=='CLOSED']
remaining=[dict(row=r['row'],function=r['function'],reason=causes[r['row']],chain_B=True,needs_Kani=False,needs_extraction=False) for r in rows if r['row'] in reviewed and r['composed_status']!='CLOSED']
spec=J(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];srows=[r for r in rows if r['function'] in spec['functions']];counts=lambda rs:dict(collections.Counter(r['composed_status'] for r in rs))
delta=dict(status='PASS',baseline='evidence/slice-s-retarget-20261104/NFY_LEDGER_DELTA.json',baseline_sha256=H(P/'NFY_LEDGER_DELTA.json'),inventory_basis=599,historical_NFX_basis=587,inventory_identity_unchanged=True,scope='Additive S-only delta, preserving the corrected 599-row inventory and concurrent D/Pool credits; no global ledger overwritten',promotions=promotions,remaining_qualified_S=remaining,S_before=prior['S_after'],S_after=counts(srows),S_roots=[dict(function=f,rows=[r['row'] for r in srows if r['function']==f],status='CLOSED' if all(r['composed_status']=='CLOSED' for r in srows if r['function']==f) else 'QUALIFIED') for f in spec['roots']],new_trust_rows=[],removed_trust_rows=[],security_target_established=False,cold_release_replay=False)
assert check_delta(base,prior,delta,certs,scan)
check=dict(status='PASS_COMPLETE_INVENTORY',selected_rows=len(certs['rows']),recursive_record_count=certs['record_count'],distinct_names=len({t['canonical_name'] for r in certs['rows'] for t in r['theorems']}),missing_references=len(gaps),missing_unique_declarations=len({r['canonical_name'] for r in gaps}),missing_modules=sorted({r['canonical_module'] for r in gaps}),gaps=gaps,all_loaded_selected_names_raw_audited=True,chain_A_missing=[],chain_B_only=all(g['canonical_module'].startswith(('NEX_','NEY_','NED_')) for g in gaps),selected_callee_denials_propagated=True)
assert check['chain_B_only']
loaded_names={q['canonical_name'] for row in certs['rows'] for q in row['theorems'] if q['canonical_module'] in {s['module'] for s in scan}}
assert loaded_names=={r['name'] for r in inventory['entries'] if r['found']}
assert {g['canonical_name'] for g in gaps}=={r['name'] for r in inventory['entries'] if not r['found']}
check.update(kernel_inventory='NGE_DECLARATION_INVENTORY.json',kernel_inventory_sha256=H(E/'NGE_DECLARATION_INVENTORY.json'),actual_owner_and_type_verified=True)
(E/'NGE_CERT_CHECK.json').write_text(json.dumps(check,indent=1)+'\n');(E/'NGE_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
lines=['# Remaining S occurrences','','Every missing auxiliary belongs to chain B; all chain A selected names are compiled, coherently loaded and raw-audited. No Kani or extraction is needed. This is a scoped additive delta, preserving the corrected 599-row inventory.','','| Row | Function | Exact missing declaration or selected-callee denial |','|---|---|---|']
for r in remaining:
 reason=r['reason'];detail='; '.join(g['canonical_name']+' (chain B)' for g in reason.get('gaps',[])) or '; '.join(reason.get('claims',[]))+' (selected chain B callee remains QUALIFIED)';lines.append('| '+r['row']+' | '+r['function']+' | '+detail+' |')
(E/'NGE_REMAINING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(promotions=len(promotions),S_after=delta['S_after'],roots_closed=sum(r['status']=='CLOSED' for r in delta['S_roots']),audit_roots=len(results),scan=summary,missing_names=check['missing_unique_declarations'])))
