"""Exact KMX positive/failing-control admission for each immutable Box-window configuration."""
from NEK_common_batch import *

def worker_copy(item,base):
 a=item['attempt'];x=cfg(item,base);name='NEK_kmx::KMX_checks::KMX_ptr_'+('wrong' if item['negative'] else 'correct')
 # The bad copy is selected by the exact KMX patch's own harness, not by a
 # new stub or a postcondition-feature inversion.
 features=x['native_command'][x['native_command'].index('--features')+1].split(',')
 features=[f for f in features if f!='NEK_invert'];x['native_command'][x['native_command'].index('--features')+1]=','.join(features)
 x['native_command'][x['native_command'].index('--harness')+1]=name;x['module']=name;x['deps_fingerprint']['support_role']='copy_configuration_control'
 rc=launch(x)
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{p.name:p.read_text() for p in b.glob({(a+'-*check.json')!r})}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
 v=verdict((E/a/'stdout.log').read_text());result=dict(attempt=a,original_receipt=item['original_receipt'],verdict=v,expected='FAIL' if item['negative'] else 'PASS',negative=item['negative'],method='exact KMX pointer control in the same deployed/empty-feature Box configuration',clause=item['clause'],selected_cfg=item['cfg'],support_role='copy_configuration_control')
 with write_lock:
  with (E/'NEK_RESULTS.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 print(a,v,flush=True)
 return result

def run(start=130):
 base=read_json(E/'NEK_COMMON_IMMUTABLE_v2.json.xz');items=read_json(E/'NEK_COMMON_BATCH_PLAN_v2.json');selected=[i for i in items if not i['negative']];plan=[]
 for i,item in enumerate(selected):
  for neg in [False,True]:
   q=dict(item);q.update(attempt=f'NEK_K{start+2*i+int(neg):03}',negative=neg);plan.append(q)
 (E/'NEK_COMMON_COPY_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
 # This routine intentionally performs no source/configuration mutation.
 with ThreadPoolExecutor(max_workers=3) as pool:
  fs=[]
  for i,item in enumerate(plan):
   if (E/item['attempt']/'receipt.json').exists():continue
   fs.append(pool.submit(worker_copy,item,base))
   if i<2:time.sleep(2)
  for f in as_completed(fs):f.result()
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 130)
