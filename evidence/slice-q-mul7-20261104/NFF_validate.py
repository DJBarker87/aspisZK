"""Additive NDT disposition: controlled windows never imply whole-row closure."""
from pathlib import Path
import json,hashlib,copy,lzma
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,msg):
 if not p:raise ValueError(msg)
def validate(closed=None,edges=None):
 audit=obj(E/'NFF_AUDIT.json');require(audit['status']=='PASS_COMBINED_HEADLINE_NFF' and audit['roots']==41,'incomplete combined ax2 audit')
 require(audit['raw_graphs_equal_collectAxioms'] and audit['standard_axioms_only'] and audit['zero_unresolved_constants'],'axiom audit failed')
 require(audit['walker_unchanged'] and audit['scanner_unchanged'],'unreviewed audit infrastructure')
 scan=audit['incoherence_scan'];require(scan['dangling']==scan['import_mismatches']==0 and scan['output_sha256']==sha(E/'NFF_LOADED_scan.jsonl'),'incoherence scan failed')
 for r in audit['results']:
  data=lzma.decompress((E/r['graph_archive']).read_bytes());require(hashlib.sha256(data).hexdigest()==r['uncompressed_sha256'],'raw graph hash drift')
  require(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'},'raw graph/axiom drift')
 native=obj(E/'NFF_NATIVE_VALIDATION.json');require(native['attempts']==90 and len(native['groups'])==32 and all(r['exact_kmx_same_payload'] for r in native['groups']),'native/control provenance missing')
 require(not native['newly_closed'] and not native['option_fn_credits'] and not native['writable_static_credits'],'quarantined/unsupported promotion')
 peer=obj(E/'NFF_NFB_VALIDATION.json');require(peer['exit_status']==0 and peer['output_sha256']==sha(E/'NFF_NFB_VALIDATOR.log'),'unchanged NEW/NET/NFB chain did not pass')
 require(peer['delta']['baseline_validator_sha256']==sha(E.parent/'slice-q-compose4-20261104/NEW_validate.py'),'baseline validator drift')
 closed=obj(E/'NFF_CLOSED.json') if closed is None else closed
 require(closed['newly_closed']==[] and all(r['status']=='OPEN' for r in closed['dot_rows'].values()),'source-only promotion rejected: full native physical installation missing')
 require(closed['roots']==obj(E.parent/'slice-q-mul6-20261104/NFE_CLOSED.json')['roots'],'unreviewed root promotion')
 edges=obj(E/'NFF_EDGES.json') if edges is None else edges
 require(edges==obj(E.parent/'slice-q-mul6-20261104/NFE_EDGES.json'),'unregistered caller edge promotion or prune')
 delta=obj(E/'NFF_LEDGER_DELTA.json');require(delta['new_count']==0 and not delta['newly_closed'] and not delta['newly_certified_incoming_edges'],'unsupported closure delta')
 require(delta['edge_total']==257 and delta['edge_inventory_sha256']==sha(E/'NFF_EDGES.json'),'edge inventory drift')
 require(not delta['sibling_combined_credit'] and not delta['security_target_established'],'incompatible sibling/security promotion')
 rows=[json.loads(s) for s in (E/'NFF_ATTEMPTS.jsonl').read_text().splitlines()];require(len(rows)==150 and len({r['attempt'] for r in rows})==150,'budget ledger mismatch')
 for module in [r['module'] for r in rows if r['kind']=='lean' and r['exit_status']==0]:
  r=next(r for r in reversed(rows) if r['kind']=='lean' and r['exit_status']==0 and r['module']==module)
  require(r['source_hashes']['NFF_generated/'+module+'.lean']==sha(E/(module+'.lean')),'compiled current-source drift: '+module)
 return dict(status='PASS_NO_PREMATURE_PROMOTION',new_NDT_rows=0,new_incoming_edges=0,raw_roots=41,coherent_modules=scan['modules'],native_window_groups=32,sibling_source_validation='PASS',sibling_combined_credit=False,budget=audit['budget'])
if __name__=='__main__':
 out=validate();tests=[]
 c=copy.deepcopy(obj(E/'NFF_CLOSED.json'));c['newly_closed']=['TX1:105'];c['dot_rows']['TX1:105']['status']='CLOSED'
 try:validate(closed=c)
 except ValueError as e:require('source-only promotion rejected' in str(e),'wrong row rejection');tests.append('source-only row promotion rejected')
 else:raise AssertionError('row mutation accepted')
 e=copy.deepcopy(obj(E/'NFF_EDGES.json'));e['edges'][0]['status']='NFF_FAKE_CLOSED'
 try:validate(edges=e)
 except ValueError as error:require('unregistered caller edge' in str(error),'wrong edge rejection');tests.append('unregistered caller edge promotion rejected')
 else:raise AssertionError('edge mutation accepted')
 out['mutations']=tests;(E/'NFF_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
