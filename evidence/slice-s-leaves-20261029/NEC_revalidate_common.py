"""Read-only audit of committed predecessor windows; no prover rerun."""
from pathlib import Path
import json,subprocess,hashlib,re,tempfile
E=Path(__file__).resolve().parent
rev='f4ff4b340c06640d911632d110d49aa92e68e50e';base='evidence/native-front4b-20261028/'
used={}
def get(p):
 b=subprocess.check_output(['git','show',rev+':'+p],stderr=subprocess.DEVNULL);used[p]=dict(revision=rev,sha256=hashlib.sha256(b).hexdigest());return b
def obj(p):return json.loads(get(p))
windows={'scalar':35,'master':37,'checkpoint':9,'lane':11,'anchor':13,'live_pool':15,'live_domain':17,'live_scalar':19,'live_root':21,'live_frontier':23,'candidate_scalar':25,'candidate_root':27,'candidate_frontier_value':31,'candidate_frontier_frame':33}
checks=[]
for w,n in windows.items():
 pair=[]
 for i in [n,n+1]:
  a=f'NDM_K{i:03d}';r=obj(base+a+'/receipt.json');log=get(base+a+'/stdout.log').decode()
  assert r['exit_status']==(0 if i==n else 1),(a,r['exit_status'])
  assert 'CBMC timed out' not in log and 'killed by signal' not in log
  assert ('VERIFICATION:- SUCCESSFUL' if i==n else 'Failed Checks: |r|') in log
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  g=obj(base+a+'-graph-check.json');assert g['exact_frozen_selected_graph']
  features={v['name']:v['features'] for v in g['resolved_features_all_crates']}
  assert {'pool-adapter','private-leaf-salts'}<=set(features['aspis-r1-cost-probe-program'])
  assert 'no-entrypoint' not in features['aspis-r1-cost-probe-program']
  lock=obj(base+a+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  patch=get(base+a+'/NDM_harness.patch').decode()
  with tempfile.TemporaryDirectory(prefix='NEC-common-') as tmp:
   root=Path(tmp)
   for name in re.findall(r'^--- a/(.+)$',patch,re.M):
    q=root/name;q.parent.mkdir(parents=True,exist_ok=True)
    q.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+name]))
   subprocess.run(['git','apply','--unsafe-paths','-'],input=patch.encode(),cwd=root,check=True,capture_output=True)
   source_checks={}
   for name,h in r['source_hashes'].items():
    if name.startswith('NDM_src/') and name.endswith('.rs'):
     rel=name[len('NDM_src/'):];q=root/rel
     assert q.exists(),(a,rel)
     assert hashlib.sha256(q.read_bytes()).hexdigest()==h,(a,rel)
     source_checks[rel]=h
   actual=(root/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
   original=subprocess.check_output(['git','show','4bb3b3f5:programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode()
   def common(s):return s[s.index('fn asq8_common('):s.index('\n#[inline(never)]\nfn transfer_statement_box(')]
   assert common(actual)==common(original),'native body changed'
  pair.append(dict(attempt=a,receipt=base+a+'/receipt.json',control=i!=n))
 checks.append(dict(window=w,pair=pair))
# Exact Box/Common interface fidelity is separately audited; it grants no
# scalar/fixed-array-only policy expansion and no new verified substitution.
fidelity=[]
for n,status in [(60,0),(61,1),(62,0),(63,1),(64,1)]:
 a=f'NDM_K{n:03d}';r=obj(base+a+'/receipt.json');log=get(base+a+'/stdout.log').decode()
 assert r['exit_status']==status and 'timed out' not in log.lower(),a
 assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'Failed Checks:') in log,a
 assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert obj(base+a+'-graph-check.json')['exact_frozen_selected_graph']
 assert obj(base+a+'-lock-check.json')['unchanged']
 get(base+a+'/NDM_harness.patch')
 fidelity.append(dict(attempt=a,exit_status=status,receipt=base+a+'/receipt.json'))
get('evidence/kani-mitig-20261028/KMX_copy_stubs.patch')
# Entire adopted Rust body remains identical; annotations alone decorate asq8_common.
frozen=subprocess.check_output(['git','show','4bb3b3f5:programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode()
body=frozen[frozen.index('fn asq8_common('):frozen.index('\n#[inline(never)]\nfn transfer_statement_box(')]
for w in checks:
 for r in w['pair']:
  # Per-attempt scratch source is pinned in receipt; retained patch reconstructs it.
  p=get(base+r['attempt']+'/NDM_harness.patch').decode()
  unchanged='\n'.join(line[1:] for line in p.splitlines() if line.startswith(' ') or line.startswith('+') and not line.startswith('+++'))
  # Sparse patch context need not contain the entire body; pin original source and exact patch.
get(base+'NDM_reference.rs.txt');get(base+'NDM_EXTRACTION_PINS.json')
(E/'NEC_COMMON_REVALIDATION.json').write_text(json.dumps(dict(status='windows audited; native semantic transport remains P6/D188',windows=checks,fidelity=fidelity,artifacts=used,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),new_kani_runs=0,new_extraction_runs=0),indent=1)+'\n')
print('audited',len(checks),'window pairs')
