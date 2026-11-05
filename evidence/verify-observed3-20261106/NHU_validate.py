"""Additive NHU admission; inherited validation is called read-only."""
from pathlib import Path
import json,hashlib,runpy,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
def read(n):return json.loads((E/n).read_text())
def validate(packet=None):
 inherited=runpy.run_path(str(R/'evidence/verify-observed2-20261106/NHG_final_validate.py'))['validate']()
 assert inherited['final_status']=='PASS' and len(inherited['new_rows'])==18
 p=read('NHU_CLOSED.json') if packet is None else packet
 assert len(p['functions'])==1
 row=p['functions'][0];assert row['rows']==['TX1:130'] and row['status']=='CLOSED'
 assert row['domain']=='deployed program feature graph, detail-phases absent, observer None; arbitrary evaluated U8 phase argument'
 assert row['modifies']=='none; no result/error/divergence, allocation, state write, callback, digest or profiling event'
 assert not row['inner_hypotheses_remaining']
 assert row['form']=='source no-op reclassification under (z)(1), deployed None only'
 src=read('NHU_MARK_SOURCE.json');assert src['status']=='PASS' and len(src['controls'])==3 and all(x['rejected'] for x in src['controls'])
 for name,attempt in [('NHU_Mark',3),('NHU_VerifyFrame',5),('NHU_COMBINED_IMPORT',6)]:
  rc=read(f'NHU_L{attempt:03}/receipt.json');assert rc['exit_status']==0
  assert hashlib.sha256((E/(name+'.lean')).read_bytes()).hexdigest()==rc['source_hashes']['NHU_generated/'+name+'.lean']
  assert all('sorryAx'not in l for l in rc['print_axioms'])
 raw=read('NHU_audit/batch0/proof0.json');assert raw['exit_status']==0 and len(raw['results'])==6
 assert {r['root'] for r in raw['results']}==set(read('NHU_AUDIT_ROOTS.json')['groups'][0])
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw['results'])
 scan=[json.loads(l) for l in (E/'NHU_LOADED_scan.jsonl').read_text().splitlines()]
 assert len(scan)==13593 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
 assert read('NHU_L012/receipt.json')['exit_status']==0
 assert not read('NHU_EDGES.json')['closed_edges']
 return dict(status='PASS',new_rows=['TX1:130'],inherited_NHG_rows=18,root137_closed=False,finish136_closed=False,prepare_op9_instantiated=False,raw_roots=6,scan_modules=len(scan),baseline='NHG_final_validate.validate read-only',checks_added_only=True,trust_added=[],trust_removed=[])
if __name__=='__main__':
 result=validate();denials=[]
 for name,edit in [
  ('promote root',lambda p:p['functions'][0].update(rows=['TX1:137'])),
  ('broaden observer',lambda p:p['functions'][0].update(domain='arbitrary observer')),
  ('write allowed',lambda p:p['functions'][0].update(modifies='transcript state')),
  ('open premise',lambda p:p['functions'][0].update(inner_hypotheses_remaining=['finish success'])),
  ('native fiction',lambda p:p['functions'][0].update(form='native Kani pass'))]:
  p=copy.deepcopy(read('NHU_CLOSED.json'));edit(p)
  try:validate(p)
  except AssertionError:denials.append(dict(name=name,rejected=True))
  else:raise AssertionError(name)
 (E/'NHU_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n')
 (E/'NHU_ADMISSION_DENIALS.json').write_text(json.dumps(denials,indent=1)+'\n')
 (E/'NHU_AUDIT.json').write_text(json.dumps(dict(status='PASS',joint='NHU_L006',raw='NHU_L009',scan='NHU_L012',roots=read('NHU_audit/batch0/proof0.json')['results'],scan_modules=result['scan_modules']),indent=1)+'\n')
 print(json.dumps(result))
