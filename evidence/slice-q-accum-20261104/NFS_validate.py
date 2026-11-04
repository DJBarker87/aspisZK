"""Checks added above unchanged NFP/NFM and NFN/NFG validator chains."""
from pathlib import Path
import sys,json,hashlib,lzma,subprocess,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-q-values-20261104'));import NFP_validate
sys.path.insert(0,str(E.parent/'slice-q-phase-20261104'));import NFN_validate
sys.path.insert(0,str(E));import NFS_native_association as native
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ROWS={'TX1:089','TX2:059','TX1:088','TX2:058'}
STANDARD={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def check_new(closed=None,edges=None,audit=None,native_report=None):
 c=obj(E/'NFS_CLOSED.json') if closed is None else closed
 e=obj(E/'NFS_EDGES.json') if edges is None else edges
 a=obj(E/'NFS_AUDIT.json') if audit is None else audit
 n=obj(E/'NFS_NATIVE_REUSE.json') if native_report is None else native_report
 need(c['headline']=='AspisR1.RPx_Deployed.deployed' and c['new_count']==4 and set(c['newly_closed'])==ROWS and set(c['rows'])==ROWS,'wrong headline or row promotion')
 need(not c['security_target_established'] and not c['cold_release_replay'] and not c['new_trust_items'],'security/trust/release scope changed')
 need(all(r['status']=='CLOSED under (ae)' for r in c['rows'].values()),'route label omitted')
 certs={r['id']:r for r in c['certificates']};need(set(certs)=={'NFS-query-values','NFS-query-loop'},'missing/extra packet')
 for cert in certs.values():
  need(cert['status']=='CLOSED under (ae)' and not cert['residual_inner_hypotheses'],'hidden inner premise or route drift')
  need(cert['root_physical_interpretation_retained'] and set(cert['four_parts'])=={'native','emitted_child_models','caller_domains_and_frames','result_state_ordered_effects'},'incomplete four-part packet')
  need(not cert['new_trust_items'] and 'reclassified' in cert['trust'],'transport trust removal')
 need(certs['NFS-query-loop']['four_parts']['emitted_child_models']['child'] in certs,'open loop child')
 ledger=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');byrow={r['row']:r['function'] for r in ledger['rows']}
 for row,entry in c['rows'].items():need(byrow[row]==entry['function'] and entry['certificate'] in certs,'wrong NDT occurrence/certificate')
 intake=obj(E.parent/'slice-q-values-20261104/NFP_EDGE_INTAKE.json');wanted={r['edge'] for r in intake if r['status']=='OPEN'}
 need(e['inventory_edge_count']==257 and e['inherited_closed']==199 and set(e['newly_closed'])==wanted and e['new_count']==16 and e['edge_closed']==215,'edge omission/deletion/double-counting')
 need({r['edge'] for r in e['overrides']}==wanted and len(e['overrides'])==16,'missing or extra edge certificate')
 for r in e['overrides']:
  need(r['status']=='CLOSED under (ae)','edge route label')
  if r['certificate']['kind']!='STATIC_UNREACHABLE':need(not r['certificate']['residual_inner_hypotheses'] and set(r['certificate']['parts'])=={'packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'},'edge part or inner premise')
 need(n==native.check(),'native/source/control/copy/rename or typed-pruning drift')
 need(len([r for r in e['overrides'] if r['certificate']['kind']=='STATIC_UNREACHABLE'])==7,'typed alternative promotion')
 manifest=obj(E/'NFS_AUDIT_ROOTS.json');need(a['status']=='PASS_COHERENT_QUERY_PACKETS' and a['root_count']==107 and len(a['roots'])==107 and {r['root'] for r in a['roots']}==set(manifest['roots']),'raw root omitted')
 need(a['raw_walk_authoritative'] and a['standard_axioms_only'] and a['walker_byte_identical_to_NEP'] and a['audit_prefix_unchanged'] and a['audit_action_unchanged'] and a['scanner_core_unchanged'],'audit implementation changed')
 need(a['driver_source_sha256']==sha(E/'NFS_ProofDriver.lean') and a['scanner_source_sha256']==sha(E/'NFS_Driver.lean'),'audit source drift')
 for r in a['roots']:
  need(set(r['walked_axioms'])<=STANDARD,'nonstandard raw axiom')
  raw=lzma.decompress((E/r['graph_archive']).read_bytes());need(hashlib.sha256(raw).hexdigest()==r['uncompressed_sha256'] and sha(E/r['graph_archive'])==r['compressed_sha256'],'raw graph bytes changed')
  measured=[json.loads(l[11:]) for l in (E/'NFS_final_audit'/(r['mode']+'.log')).read_text().splitlines() if l.startswith('NEP_RESULT ')]
  got=next(x for x in measured if x['root']==r['root']);need(all(r[k]==v for k,v in got.items()),'graph differs from measured result')
 need(len(a['fixtures'])==8 and all(r['equal'] for r in a['fixtures']),'fixture controls omitted')
 oldfixtures=obj(E.parent/'slice-q-phase-20261104/NFN_AUDIT.json')['fixtures']
 need({r['root']:r['walked_axioms'] for r in a['fixtures']}=={r['root']:r['walked_axioms'] for r in oldfixtures},'fixture expectations changed')
 scan=a['incoherence_scan'];need(scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0 and scan['output_sha256']==sha(E/'NFS_LOADED_scan.jsonl'),'incoherent closure')
 attempts=[json.loads(l) for l in (E/'NFS_ATTEMPTS.jsonl').read_text().splitlines()];need(len(attempts)<=90 and len({r['attempt'] for r in attempts})==len(attempts),'budget/duplicate attempt')
 for r in attempts:
  for k in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']:need(k in r,'missing section6 field '+k)
  if r['kind']=='prelaunch':continue
  ad=obj(E/(r['attempt']+'-admission.json'));need(ad['exit']==0 and ad['reservation']['allowed'] is True,'unadmitted scope')
  need(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(r['swaps'])=='0','resource drift')
 accepted=manifest['new_modules']+['NFS_AccumPart00','NFS_AccumPart01','NFS_AccumPart02','NFS_Folds','NFS_COMBINED_IMPORT','NFS_ProofDriver','NFS_Driver']
 for m in accepted:
  good=[r for r in attempts if r['kind']=='lean' and r['module']==m and r['exit_status']==0]
  need(bool(good) and good[-1]['source_hashes']['NFS_generated/'+m+'.lean']==sha(E/(m+'.lean')),'current accepted source not compiled '+m)
 gate=obj(E/'NFS_L089/receipt.json');need(gate['exit_status']==0,'final gate failed')
 children=obj(E/'NFS_final_audit/NFS_CHILD_ATTEMPTS.json');need(len(children)==31 and all(r['exit_status']==0 for r in children),'final timed children incomplete')
 delta=obj(E/'NFS_LEDGER_DELTA.json');need(delta['new_count']==4 and set(delta['newly_closed'])==ROWS and delta['new_edge_count']==16 and delta['edge_closed']==215 and delta['query_values_incoming_edge_closed'] and not delta['sibling_credit_double_counted'],'delta drift')
 for pin in obj(E/'NFS_REUSED_INPUTS.json'):need(sha(R/pin['path'])==pin['sha256'],'reused input changed')
 return dict(status='PASS_NDT_QUERY_ROWS_UNDER_AE',new_NDT_rows=4,new_edges=16,edge_closed=215,edge_total=257,raw_roots=107,coherent_modules=scan['modules'],security_target_established=False,cold_release_replay=False,kani_used=0,kani_limit=30,lean_audit_used=len(attempts),lean_audit_limit=90,extraction_used=0,extraction_limit=1)
def validate():
 old=NFP_validate.validate();need(old['status']=='PASS_ADDITIVE_SUPPORT_ONLY','NFP chain drift')
 geometry=NFN_validate.validate();need(geometry==obj(E/'NFS_NFN_REVALIDATION.json'),'NFN chain drift')
 for generator in ['NFS_generate.py','NFS_folds_generate.py']:
  r=subprocess.run([sys.executable,str(E/generator),'--check'],capture_output=True,text=True);need(r.returncode==0,'regeneration drift '+generator)
 return check_new()
if __name__=='__main__':
 result=validate();tests=[]
 c=obj(E/'NFS_CLOSED.json');c['rows']['TX1:089']['status']='CLOSED';tests.append(('missing ae qualification',dict(closed=c)))
 c=obj(E/'NFS_CLOSED.json');c['newly_closed'].append('TX1:001');tests.append(('out-of-slice promotion',dict(closed=c)))
 c=obj(E/'NFS_CLOSED.json');c['certificates'][0]['residual_inner_hypotheses']=['assume whole child reply'];tests.append(('hidden child result',dict(closed=c)))
 c=obj(E/'NFS_CLOSED.json');c['certificates'][1]['four_parts']['emitted_child_models']['child']='OPEN';tests.append(('open loop child',dict(closed=c)))
 e=obj(E/'NFS_EDGES.json');e['overrides'].pop();tests.append(('missing edge',dict(edges=e)))
 e=obj(E/'NFS_EDGES.json');e['edge_closed']+=2;tests.append(('sibling double count',dict(edges=e)))
 a=obj(E/'NFS_AUDIT.json');a['roots'][0]['walked_axioms'].append('sorryAx');tests.append(('nonstandard raw axiom',dict(audit=a)))
 a=obj(E/'NFS_AUDIT.json');a['roots'].pop();tests.append(('omitted raw root',dict(audit=a)))
 for key in ['dangling','incompatible_owners','import_mismatches']:
  a=obj(E/'NFS_AUDIT.json');a['incoherence_scan'][key]=1;tests.append((key,dict(audit=a)))
 a=obj(E/'NFS_AUDIT.json');a['fixtures'].pop();tests.append(('missing fixture',dict(audit=a)))
 n=obj(E/'NFS_NATIVE_REUSE.json');n['failing_controls']=0;tests.append(('missing native controls',dict(native_report=n)))
 rejected=[]
 for label,params in tests:
  try:check_new(**params)
  except ValueError:rejected.append(label)
  else:raise AssertionError('mutation admitted '+label)
 result['mutations_rejected']=rejected;(E/'NFS_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
