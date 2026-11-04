"""Add checks to the unchanged NFI/NFF/NEW/NET disposition; no upstream waiver."""
from pathlib import Path
import json,hashlib,lzma,sys,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul8-20261104'
sys.path.insert(0,str(P));import NFI_validate as prior
sys.path.insert(0,str(E));import NFM_native_check as native
import NFM_certificates as cert
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,message):
 if not ok:raise ValueError(message)
def validate(closed=None,edges=None,certificates=None,audit=None):
 inherited=prior.validate();require(inherited['new_NDT_rows']==0,'baseline disposition changed')
 n=native.check();require(n==obj(E/'NFM_NATIVE_VALIDATION.json'),'native validation drift')
 a=obj(E/'NFM_AUDIT.json') if audit is None else audit
 require(a['status']=='PASS_COMBINED_HEADLINE_NFM' and a['roots']==124 and a['new_roots']==49,'audit incomplete')
 require(a['walker_unchanged'] and a['audit_action_unchanged'] and a['scanner_core_unchanged'],'unadmitted audit change')
 require(a['raw_graphs_equal_collectAxioms'] and a['standard_axioms_only'] and a['zero_unresolved_constants'],'axiom admission failed')
 require(a['driver_source_sha256']==sha(E/'NFM_Driver.lean'),'driver source drift')
 scan=a['incoherence_scan'];require(scan['dangling']==scan['import_mismatches']==0 and scan['output_sha256']==sha(E/'NFM_LOADED_scan.jsonl'),'incoherence scan drift')
 names=set()
 for r in a['results']:
  raw=lzma.decompress((E/r['graph_archive']).read_bytes());require(hashlib.sha256(raw).hexdigest()==r['uncompressed_sha256'],'raw graph drift')
  require(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'},'axiom mismatch')
  names.update(raw.decode().splitlines())
 require(len(a['fixtures'])==8 and all(r['equal'] for r in a['fixtures']),'ax2 controls missing')
 expected_c,expected_e,expected_closed,expected_d=cert.expected()
 c=obj(E/'NFM_CERTIFICATES.json') if certificates is None else certificates
 e=obj(E/'NFM_EDGES.json') if edges is None else edges
 closed=obj(E/'NFM_CLOSED.json') if closed is None else closed
 require(c==expected_c,'incomplete or unreviewed hybrid certificate')
 require(e==expected_e,'unregistered caller edge change/prune')
 require(closed==expected_closed,'unregistered row/root promotion')
 require(obj(E/'NFM_LEDGER_DELTA.json')==expected_d,'ledger delta drift')
 # Check every referenced theorem is in the actually walked combined closure.
 refs=set()
 for row in c:
  require(row['parts']==['result','state','ordered_effects','native_association'] and not row['remaining_inner_hypotheses'],'four-part bridge incomplete')
  require(not row['whole_native_output_hypothesis'] and not row['private_stepby_relation_hypothesis'],'whole-result/state relation assumed')
  for k in ['primitive_laws','native_product_theorems','state_theorems','control_theorems','caller_domain_theorems']:refs.update(row[k])
  refs.add(row['model_theorem'])
 for edge in e['edges']:
  if edge['certificate'] and edge['certificate'].get('id','').startswith('NFM-edge:'):refs.update(edge['model_domain_theorems'])
 require(refs<=names,'unresolved theorem reference: '+str(sorted(refs-names)))
 # NDT's dependencies are local whole-body packet status, not an assertion
 # that every incoming application has already established its domain.
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');byrow={r['row']:r for r in base['rows']};edgemap={r['edge']:r for r in e['edges']}
 derived=[]
 for row in c:
  original=byrow[row['row']];require(original['function']==row['function'],'wrong occurrence')
  require(all(dep==cert.ONE for dep in original['open_transitive_dependencies']),'unbridged local dependency')
  obligations=[]
  for obligation in original['caller_domain_obligations']:
   o=copy.deepcopy(obligation)
   if o['id'].startswith('call-domain:'):
    edge=edgemap[o['caller']+' -> '+o['callee']];require(edge['status']=='CLOSED' and edge['certificate'],'open call domain')
    o['status']='CLOSED';o['discharged_by']=edge['certificate']['id']
   else:
    expr=o['call'].get('expression',o['call'].get('syntax'))
    require(isinstance(expr,str),'missing external syntax')
    require(any(token in expr for token in ['step_by','core::cmp::min','try_into','unwrap','u64::from']),'unclassified external: '+expr)
    o['status']='CLOSED';o['discharged_by']=dict(certificate=row['id'],classification='Exact std/scalar operation in native cut plus emitted-definition law; retained TrustedStd/P6 qualifications',native='NFM_NATIVE_VALIDATION.json',model=row['control_theorems']+row['state_theorems'])
   obligations.append(o)
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in obligations),'NDT obligations remain')
  derived.append(dict(row=row['row'],function=row['function'],frozen_body_sha256=row['source_body_sha256'],bridge_status='CLOSED',composed_status='CLOSED',selected_claims=[row['id']],named_hypotheses=[],caller_domain_obligations=obligations,inventory_domain_obligations=[dict(**{k:v for k,v in old.items() if k not in ['status','discharged_by']},status='CLOSED',discharged_by=dict(certificate=row['id'],domain=row['domain'],upstream_boundary_retained=True)) for old in original['inventory_domain_obligations']],open_transitive_dependencies=[],domain=row['domain'],retained_trust=row['trust']))
 require(len(e['edges'])==257 and len(expected_d['newly_certified_edges'])==12,'edge inventory pruned')
 require(not closed['security_target_established'] and not expected_d['query_values_incoming_edge_closed'],'upstream/security promotion')
 return dict(status='PASS_NDT_FOUR_DOT_ROWS',new_NDT_rows=4,new_edges=12,edge_closed=expected_d['edge_closed'],raw_roots=124,new_top_theorems=49,coherent_modules=scan['modules'],native_groups=25,reused_native_groups=39,budget=a['budget'],remaining_query_values_incoming='OPEN',derived_rows=derived,baseline=inherited)
if __name__=='__main__':
 x=validate();tests=[]
 mutations=[]
 closed=copy.deepcopy(obj(E/'NFM_CLOSED.json'));closed['roots'][next(iter(closed['roots']))]='CLOSED';mutations.append(('root promotion',dict(closed=closed)))
 edges=copy.deepcopy(obj(E/'NFM_EDGES.json'));target=next(e for e in edges['edges'] if e['caller'].endswith('candidate.rs::query_values') and e['callee']==cert.FOUR);target['status']='CLOSED';mutations.append(('incoming edge promotion',dict(edges=edges)))
 cs=copy.deepcopy(obj(E/'NFM_CERTIFICATES.json'));cs[0]['whole_native_output_hypothesis']=True;mutations.append(('whole-output premise',dict(certificates=cs)))
 cs=copy.deepcopy(obj(E/'NFM_CERTIFICATES.json'));cs[0]['remaining_inner_hypotheses']=['unproved physical execution'];mutations.append(('missing physical certificate',dict(certificates=cs)))
 audit=copy.deepcopy(obj(E/'NFM_AUDIT.json'));audit['results'][0]['walked_axioms'].append('sorryAx');mutations.append(('nonstandard axiom',dict(audit=audit)))
 for label,kwargs in mutations:
  try:validate(**kwargs)
  except ValueError:tests.append(label)
  else:raise AssertionError('mutation admitted: '+label)
 (E/'NFM_DERIVED_ROWS.json').write_text(json.dumps(x.pop('derived_rows'),indent=2)+'\n')
 x['mutations_rejected']=tests;(E/'NFM_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n')
 print(json.dumps({k:v for k,v in x.items() if k!='baseline'}))
