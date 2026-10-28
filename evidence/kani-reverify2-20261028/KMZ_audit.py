from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('KMZ_*/receipt.json')):
 rc=json.loads(p.read_text());a=rc['attempt'];log=(p.parent/'stdout.log').read_text()
 if 'timed out' in log.lower() or 'VERIFICATION:- TIMEOUT' in log:result='TIMEOUT'
 elif rc['exit_status']==124:result='TIMEOUT'
 elif 'VERIFICATION:- SUCCESSFUL' in log or rc['kind'] in ['lean','rust'] and rc['exit_status']==0:result='PASS'
 elif 'VERIFICATION:- FAILED' in log:result='COUNTEREXAMPLE'
 elif rc['exit_status'] in [-9,137] or 'out of memory' in log.lower() or 'sigkill' in log.lower():result='RESOURCE_LIMIT'
 else:result='ERROR'
 failures=[]
 for block in re.split(r'\nCheck ',log)[1:]:
  head=block.split('\n\n')[0]
  if 'Status: FAILURE' in head:failures.append(head)
 graph=E/(a+'-graph.json');g=json.loads(graph.read_text()) if graph.exists() else {}
 if rc['kind'] in ['kani','rust']:
  assert g.get('allowed') is True,(a,'graph admission')
  assert g.get('unchanged') is True,(a,'lock postcheck')
 assert rc['kmx_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert rc['kmx_stub_file_sha256']=='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
 if 'KMX_stubs.rs' in rc['source_hashes']:assert rc['source_hashes']['KMX_stubs.rs']==rc['kmx_stub_file_sha256']
 assert rc['swaps']=='0',(a,rc['swaps'])
 if rc['kind']=='lean' and result=='PASS':
  assert rc['print_axioms'],a
  for line in rc['print_axioms']:
   if '[' in line:assert set(line.split('[',1)[1].split(']',1)[0].replace(' ','').split(','))<= {'propext','Classical.choice','Quot.sound'},(a,line)
 row=dict(attempt=a,kind=rc['kind'],result=result,negative_control=rc.get('negative_control',False),parent=rc.get('parent_gate'),split=rc.get('split'),exit_status=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],failures=failures,solver_concrete_playback='Concrete playback unit test for' in log,receipt=str(p.relative_to(E)))
 if row['negative_control'] and result=='COUNTEREXAMPLE':assert len(failures)==1,(a,failures)
 row['graph_receipt']=a+'-graph.json' if rc['kind'] in ['kani','rust'] else None
 rows.append(row)
 if rc['kind']=='kani':(p.parent/'classification.json').write_text(json.dumps(row,indent=2)+'\n')
(E/'KMZ_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
from collections import Counter
print(dict(Counter((x['kind'],x['result']) for x in rows)))
