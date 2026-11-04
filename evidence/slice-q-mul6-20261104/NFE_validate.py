"""Fail-closed additive slice-Q disposition; unchanged baseline replay is pinned.

A packaging pass or source-only packet is never accepted as a native row recipe.
"""
from pathlib import Path
import json,hashlib,lzma,subprocess,re,copy,difflib,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,msg):
 if not b:raise ValueError(msg)
def validate(closed=None,edges=None):
 prior=E.parent/'slice-q-compose4-20261104';pin=obj(E/'NFE_BASELINE_VALIDATOR_RECEIPT.json')
 require(pin['exit_status']==0 and pin['validator_sha256']==sha(prior/'NEW_validate.py'),'unchanged baseline validator evidence')
 require(pin['output_sha256']==sha(E/'NFE_BASELINE_VALIDATOR.log'),'baseline output drift')
 require(json.loads((E/'NFE_BASELINE_VALIDATOR.log').read_text())==obj(prior/'NEW_LEDGER_DELTA.json'),'inherited complete slice-Q replay result differs')
 rt=obj(E/'NFE_RETARGET.json');require(len(rt['relations'])==4 and len(rt['provenance'])==51,'retarget inventory incomplete')
 cohort=json.loads(lzma.decompress((E/'NFE_COHORT_IMPORTS.json.xz').read_bytes()));by={r['module']:r for r in cohort}
 for row in rt['relations']:
  a=subprocess.check_output(['git','show',rt['source_revision']+':'+row['original_path']],cwd=R,text=True)
  b=by[row['headline']]['source_text'];strip=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))
  require(hashlib.sha256(a.encode()).hexdigest()==row['original_sha256'] and hashlib.sha256(b.encode()).hexdigest()==row['headline_sha256'],'source relation drift')
  require(strip(a)==strip(b) and hashlib.sha256(strip(a).encode()).hexdigest()==row['nonimport_body_sha256'],'semantic counterpart difference')
  require(row['NER_source_verified'] and row['NER_object_sha256']==by[row['headline']]['sha256'],'NER relation pin drift')
 for row in rt['provenance']:require(sha(E/(row['new_module']+'.lean'))==row['destination_sha256'],'consumer source drift')
 audit=obj(E/'NFE_AUDIT.json');require(audit['status']=='PASS_COMBINED_HEADLINE_FOREST' and audit['roots']==110 and audit['walker_unchanged'] and audit['scanner_unchanged'],'audit incomplete')
 require(audit['standard_axioms_only'] and audit['raw_graphs_equal_collectAxioms'] and audit['zero_unresolved_constants'],'audit failed')
 require(audit['incoherence_scan']['dangling']==audit['incoherence_scan']['import_mismatches']==0,'incoherent imports')
 require(audit['incoherence_scan']['output_sha256']==sha(E/'NFE_LOADED_scan.jsonl'),'scan output drift')
 for p in E.glob('NFE_L*/receipt.json'):
  r=obj(p);require(r['exit_status']==0,'failed own scope')
  if r['kind']=='lean':
   for name,h in r['source_hashes'].items():
    if name.endswith('.lean'):require(sha(E/Path(name).name)==h,'compiled source changed after receipt')
 closed=obj(E/'NFE_CLOSED.json') if closed is None else closed
 require(closed['newly_closed']==[] and all(r['status']=='OPEN' for r in closed['dot_rows'].values()),'native association and incoming physical/caller certificate missing; source-only promotion rejected')
 edges=obj(E/'NFE_EDGES.json') if edges is None else edges
 require(edges==obj(prior/'NEW_EDGES.json'),'unregistered incoming edge promotion')
 delta=obj(E/'NFE_LEDGER_DELTA.json');require(delta['new_count']==0 and delta['newly_closed']==[] and delta['newly_certified_incoming_edges']==[],'unsupported closure delta')
 require(delta['edge_inventory_sha256']==sha(E/'NFE_EDGES.json') and delta['edge_total']==257,'edge inventory drift')
 require(not delta['security_target_established'],'unsupported security claim')
 return dict(status='PASS_NO_PREMATURE_PROMOTION',new_dot_closed=0,new_incoming_edges=0,headline_packaging='PASS',combined_raw_roots=110,coherent_modules=audit['incoherence_scan']['modules'],baseline=delta['baseline_validated_delta'],remaining=closed['remaining_inner_hypotheses'])
if __name__=='__main__':
 result=validate()
 if '--tests' in sys.argv:
  c=copy.deepcopy(obj(E/'NFE_CLOSED.json'));c['newly_closed']=['TX1:105'];c['dot_rows']['TX1:105']['status']='CLOSED'
  try:validate(closed=c)
  except ValueError as e:require('source-only promotion rejected' in str(e),'wrong rejection')
  else:raise AssertionError('source-only row promotion accepted')
  edges=copy.deepcopy(obj(E/'NFE_EDGES.json'));edge=next(e for e in edges['edges'] if 'fast_dots.rs::four_dots' in e['edge'] and e['status']!='CLOSED');edge['status']='CLOSED'
  try:validate(edges=edges)
  except ValueError as e:require('unregistered incoming edge promotion' in str(e),'wrong edge rejection')
  else:raise AssertionError('unregistered edge accepted')
  result['mutation_tests']='PASS: source-only row and incoming edge promotions rejected'
 print(json.dumps(result))
