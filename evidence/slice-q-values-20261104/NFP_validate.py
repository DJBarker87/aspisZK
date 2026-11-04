"""Checks added above unchanged NFM validation; never a row-closure waiver."""
from pathlib import Path
import sys,json,hashlib,lzma,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'slice-q-mul9-20261104'));import NFM_validate as prior
sys.path.insert(0,str(E));import NFP_native_check as native
import NFP_disposition as disposition
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise ValueError(m)
def validate(closed=None,edges=None,audit=None,native_report=None):
 inherited=prior.validate();need(inherited['status']=='PASS_NDT_FOUR_DOT_ROWS' and inherited['new_NDT_rows']==4,'inherited validation changed')
 expected_c,expected_e,expected_d=disposition.expected()
 c=obj(E/'NFP_CLOSED.json') if closed is None else closed;e=obj(E/'NFP_EDGES.json') if edges is None else edges
 need(c==expected_c,'unregistered row/root promotion');need(e==expected_e,'unregistered edge promotion or inventory prune')
 need(obj(E/'NFP_LEDGER_DELTA.json')==expected_d,'delta drift')
 ledger=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');byrow={r['row']:r for r in ledger['rows']}
 for row,f in disposition.ROWS.items():need(byrow[row]['function']==f,'wrong NDT occurrence')
 n=native.check();supplied=obj(E/'NFP_NATIVE_VALIDATION.json') if native_report is None else native_report
 need(n==supplied,'native support receipt drift')
 a=obj(E/'NFP_AUDIT.json') if audit is None else audit
 need(a['status']=='PASS_COHERENT_SUPPORT_NOT_QUERY_ROW_CLOSURE' and a['roots']==59 and a['new_top_theorems']==50,'incomplete support audit')
 need(a['walker_unchanged'] and a['audit_action_unchanged'] and a['scanner_core_unchanged'],'audit implementation changed')
 need(a['raw_graphs_equal_collectAxioms'] and a['standard_axioms_only'] and a['zero_unresolved_constants'],'axiom admission failed')
 need(a['driver_source_sha256']==sha(E/'NFP_Driver.lean'),'driver source drift')
 need(a['query_rows_closed']==0 and a['legacy_accumulation_packet_excluded'] and not a['cold_release_replay'],'failed packet/cold replay promotion')
 manifest=obj(E/'NFP_AUDIT_ROOTS.json');wanted=set(manifest['roots'])|{'AspisR1.NFM_Single.domains','AspisR1.NFG_PushRoot.private_domains'}
 need({r['root'] for r in a['results']}==wanted and len(a['results'])==len(wanted),'root omitted')
 for r in a['results']:
  raw=lzma.decompress((E/r['graph_archive']).read_bytes());need(hashlib.sha256(raw).hexdigest()==r['uncompressed_sha256'] and sha(E/r['graph_archive'])==r['compressed_sha256'],'graph bytes changed')
  need(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'},'nonstandard or unequal axioms')
  logs=[json.loads(l[len('NEP_RESULT '):]) for l in (E/r['attempt']/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
  measured=next((x for x in logs if x['root']==r['root']),None)
  need(measured is not None and all(r[k]==v for k,v in measured.items()),'reported graph differs from measured graph')
 need(len(a['fixtures'])==8 and all(r['equal'] and r['walked_axioms']==r['collect_axioms'] for r in a['fixtures']),'fixture controls missing')
 scan=a['incoherence_scan'];need(scan['dangling']==scan['import_mismatches']==0 and scan['output_sha256']==sha(E/'NFP_LOADED_scan.jsonl'),'scan drift')
 attempts=[json.loads(l) for l in (E/'NFP_ATTEMPTS.jsonl').read_text().splitlines()];formal=[r for r in attempts if r['kind']!='kani']
 need(len(attempts)==136 and len(formal)==60,'budget mismatch')
 for r in attempts:
  ad=obj(E/(r['attempt']+'-admission.json'));need(ad['exit']==0 and ad['reservation']['allowed'] is True,'unadmitted scope')
  need(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'scope cap drift')
  for key in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']:need(key in r,'missing section6 field: '+key)
 for m in manifest['modules']:
  good=[r for r in formal if r['kind']=='lean' and r['module']==m and r['exit_status']==0]
  need(bool(good) and good[-1]['source_hashes']['NFP_generated/'+m+'.lean']==sha(E/(m+'.lean')),'accepted source not compiled')
 return dict(status='PASS_ADDITIVE_SUPPORT_ONLY',new_NDT_rows=0,new_edges=0,inherited_NFM_rows=4,edge_closed=199,edge_total=257,raw_roots=59,new_top_theorems=50,coherent_modules=scan['modules'],budget=expected_d['budget'],security_target_established=False,baseline_status=inherited['status'])
if __name__=='__main__':
 result=validate();mutations=[]
 c=obj(E/'NFP_CLOSED.json');c['rows']['TX1:089']['status']='CLOSED under (ae)';mutations.append(('query row promotion',dict(closed=c)))
 c=obj(E/'NFP_CLOSED.json');c['root_status']='CLOSED';mutations.append(('loop root promotion',dict(closed=c)))
 e=obj(E/'NFP_EDGES.json');e['overrides']=[dict(status='CLOSED under (ae)')];mutations.append(('incoming edge promotion',dict(edges=e)))
 a=obj(E/'NFP_AUDIT.json');a['results'][0]['walked_axioms'].append('sorryAx');mutations.append(('nonstandard axiom',dict(audit=a)))
 a=obj(E/'NFP_AUDIT.json');a['legacy_accumulation_packet_excluded']=False;mutations.append(('failed packet import waiver',dict(audit=a)))
 n=obj(E/'NFP_NATIVE_VALIDATION.json');n['excluded'].remove('NFP_K059');mutations.append(('timed-out context promotion',dict(native_report=n)))
 a=obj(E/'NFP_AUDIT.json');a['results'].pop();mutations.append(('omitted ax2 root',dict(audit=a)))
 rejected=[]
 for label,args in mutations:
  try:validate(**args)
  except ValueError:rejected.append(label)
  else:raise AssertionError('mutation admitted: '+label)
 result['mutations_rejected']=rejected;(E/'NFP_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
