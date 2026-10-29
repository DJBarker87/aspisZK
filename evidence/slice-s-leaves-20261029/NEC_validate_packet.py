"""Lane-owned strict read-only evidence validation, never a prover replacement."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,tempfile
E=Path(__file__).resolve().parent
SHA='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def raw(p):
 p=E/p
 return p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
def obj(p):return json.loads(raw(p))
def native_pair(positive,negative,marker):
 rows=[]
 for a,control in [(positive,False),(negative,True)]:
  r=obj(a+'/receipt.json');log=raw(a+'/stdout.log').decode()
  assert r['exit_status']==int(control),(a,r['exit_status'])
  assert 'CBMC timed out' not in log and 'unwinding assertion' not in log.lower(),a
  assert ('Failed Checks: '+marker if control else 'VERIFICATION:- SUCCESSFUL') in log,a
  assert r['copy_patch_sha256']==SHA
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert str(r['swaps'])=='0'
  lc=obj(a+'-lock-check.json');assert lc['before']==lc['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert obj(a+'-lock-check.json')['unchanged']
  assert obj(a+'-graph-check.json')['exact_frozen_selected_graph']
  if (E/(a+'-actual-graph-check.json')).exists():
   assert obj(a+'-actual-graph-check.json')['exact_frozen_selected_graph']
  else:
   audit=obj('NEC_FEATURE_REVALIDATION.json')
   prior=next(v for v in audit['prior_runs'] if v['attempt']==a)
   assert prior['same_manifest'] and prior['same_features']
   assert hashlib.sha256(raw(audit['checked_context'])).hexdigest()==audit['actual_graph_sha256']
   assert obj(audit['checked_context'])['exact_frozen_selected_graph']
  patch=raw(a+'/NEC_harness.patch')
  with tempfile.TemporaryDirectory(prefix='NEC-packet-') as temp:
   root=Path(temp)
   for name in re.findall(r'^--- a/(.+)$',patch.decode(),re.M):
    p=root/name;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+name]))
   subprocess.run(['git','apply','--unsafe-paths','-'],input=patch,cwd=root,check=True,capture_output=True)
   checked={}
   for name,h in r['source_hashes'].items():
    if name.startswith('NEC_src/') and name.endswith('.rs'):
     q=root/name[len('NEC_src/'):]
     data=q.read_bytes() if q.exists() else subprocess.check_output(['git','show','4bb3b3f5:'+name[len('NEC_src/'):]])
     assert hashlib.sha256(data).hexdigest()==h,(a,name)
     checked[name]=h
  rows.append(dict(attempt=a,module=r['module'],control=control,receipt=a+'/receipt.json',patch_sha256=hashlib.sha256(patch).hexdigest(),rust_source_hashes=checked))
 assert rows[0]['module']==rows[1]['module'],'renamed target'
 return rows
if __name__=='__main__':
 import sys
 pairs=json.loads((E/sys.argv[1]).read_text());out=[]
 for p in pairs:out.append(native_pair(*p))
 (E/sys.argv[2]).write_text(json.dumps(dict(pairs=out,copy_patch_sha256=SHA,new_prover_runs=0),indent=1)+'\n')
 print('validated',len(out),'pairs')
