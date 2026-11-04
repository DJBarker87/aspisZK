"""Additive NFF/NEW/NET/NFB disposition; no missing physical instance is waived."""
from pathlib import Path
import json,sys,hashlib,lzma,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul7-20261104'
sys.path.insert(0,str(P));import NFF_validate as prior
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,message):
 if not ok:raise ValueError(message)
def validate(closed=None,edges=None):
 inherited=prior.validate()
 require(inherited['new_NDT_rows']==0,'inherited delta drift')
 a=obj(E/'NFI_AUDIT.json');require(a['status']=='PASS_COMBINED_HEADLINE_NFI' and a['roots']==75,'combined audit incomplete')
 require(a['walker_unchanged'] and a['scanner_unchanged'] and a['standard_axioms_only'] and a['raw_graphs_equal_collectAxioms'] and a['zero_unresolved_constants'],'audit admission failed')
 require(a['incoherence_scan']['dangling']==a['incoherence_scan']['import_mismatches']==0 and sha(E/'NFI_LOADED_scan.jsonl')==a['incoherence_scan']['output_sha256'],'incoherence scan drift')
 require(a['driver_source_sha256']==sha(E/'NFI_Driver.lean'),'driver changed after audit')
 for r in a['results']:
  data=lzma.decompress((E/r['graph_archive']).read_bytes());require(hashlib.sha256(data).hexdigest()==r['uncompressed_sha256'],'raw graph drift')
  require(r['equal'] and set(r['collect_axioms'])==set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},'nonstandard/root axiom mismatch')
 rows=[json.loads(s) for s in (E/'NFI_ATTEMPTS.jsonl').read_text().splitlines()]
 require(len(rows)==len({r['attempt'] for r in rows})==150,'attempt ledger missing/duplicated')
 require(sum(r['kind']=='kani' for r in rows)==100,'Kani budget mismatch')
 require(sum(r['kind']!='kani' for r in rows)==50,'Lean/audit budget mismatch')
 for module in {r['module'] for r in rows if r['kind']=='lean' and r['exit_status']==0}:
  r=next(r for r in reversed(rows) if r['kind']=='lean' and r['module']==module and r['exit_status']==0)
  require(r['source_hashes']['NFI_generated/'+module+'.lean']==sha(E/(module+'.lean')),'current source not compiled: '+module)
  require(all('sorryAx' not in s for s in r['print_axioms']),'failed draft promoted')
 n=obj(E/'NFI_NATIVE_VALIDATION.json');require(n['attempts']==100 and len(n['groups'])==39 and not n['newly_closed'],'native provenance incomplete/unsupported promotion')
 require(not n['option_fn_credits'] and not n['writable_static_credits'] and not n['contracts'],'quarantined/contract promotion')
 require(obj(E/'NFI_SOURCE_PREFLIGHT.json')['mutations_rejected'] and not obj(E/'NFI_SOURCE_PREFLIGHT.json')['full_native_execution_instance'],'source-only instance promotion')
 c=obj(E/'NFI_CLOSED.json') if closed is None else closed
 require(c['newly_closed']==[] and all(r['status']=='OPEN' for r in c['dot_rows'].values()),'physical-instance gap: row promotion rejected')
 require(c['roots']==obj(P/'NFF_CLOSED.json')['roots'],'root promotion rejected')
 e=obj(E/'NFI_EDGES.json') if edges is None else edges
 require(e==obj(P/'NFF_EDGES.json'),'unregistered caller edge promotion or prune')
 d=obj(E/'NFI_LEDGER_DELTA.json');require(d['new_count']==0 and not d['newly_closed'] and not d['newly_certified_incoming_edges'],'delta promotion rejected')
 require(d['edge_total']==257 and d['edge_inventory_sha256']==sha(E/'NFI_EDGES.json') and not d['sibling_combined_credit'] and not d['security_target_established'],'edge/trust/security drift')
 return dict(status='PASS_NO_PHYSICAL_INSTANCE_PROMOTION',new_NDT_rows=0,new_incoming_edges=0,raw_roots=75,coherent_modules=a['incoherence_scan']['modules'],native_window_groups=39,budget=a['budget'],baseline_validator_sha256=sha(P/'NFF_validate.py'),inherited=inherited)
if __name__=='__main__':
 x=validate();tests=[]
 c=copy.deepcopy(obj(E/'NFI_CLOSED.json'));c['newly_closed']=['TX1:105'];c['dot_rows']['TX1:105']['status']='CLOSED'
 try:validate(closed=c)
 except ValueError as err:require('physical-instance gap' in str(err),'wrong row mutation rejection');tests.append('physical row promotion rejected')
 else:raise AssertionError('row mutation admitted')
 e=copy.deepcopy(obj(E/'NFI_EDGES.json'));e['edges'][0]['status']='NFI_FAKE_CLOSED'
 try:validate(edges=e)
 except ValueError as err:require('caller edge promotion' in str(err),'wrong edge mutation rejection');tests.append('caller edge promotion rejected')
 else:raise AssertionError('edge mutation admitted')
 x['mutations']=tests;(E/'NFI_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['status','new_NDT_rows','new_incoming_edges','raw_roots','coherent_modules','native_window_groups','mutations']}))
