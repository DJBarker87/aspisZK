"""Read-only revalidation of retained native packets. No solver/compiler launch."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 p=Path(p)
 if p.is_file():return p.read_bytes()
 return subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
def obj(p):return json.loads(read(p))
P=R/'evidence/transcript-scalars-20261105'
kmx=R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
assert sha(read(kmx))=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
files={};rows=[]
def pin(p):
 b=read(p);files[str(p.relative_to(R))]=dict(sha256=sha(b),bytes=len(b));return b
for i in range(7,43,2):
 pair=[]
 for j in [i,i+1]:
  a=f'NGT_K{j:03}';d=P/a;r=json.loads(pin(d/'receipt.json'));negative=j==i+1
  assert r['exit_status']==int(negative),(a,'exit')
  s=pin(d/'stdout.log').decode();assert ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in s
  assert 'Manual Harness Summary:' in s and not re.search(r'(?i)timed out|timeout reached|out of memory',s)
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert r['env']['CARGO_NET_OFFLINE']=='true';assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--target-dir' in r['native_command'];target=r['native_command'][r['native_command'].index('--target-dir')+1];assert target.endswith('/NGT_target');assert '--locked' not in r['native_command']
  assert ('NGT_invert' in r['env'].get('RUSTFLAGS',''))==negative
  for n,h in r['source_hashes'].items():assert sha(pin(d/'sources'/n))==h,(a,n)
  harnesses=[n for n in r['source_hashes'] if n.endswith(('/NGT_sampler.rs','/NGT_native.rs'))]
  for n in harnesses:
   t=read(d/'sources'/n).decode();assert not re.search(r'\bstatic\s+(?:mut\s+)?\w+\s*:',t)
   assert 'Option<fn' not in t and 'stub_verified' not in t
   assert 'KMX_copy_nonoverlapping' in t
  g=json.loads(pin(P/(a+'-graph-check.json')));assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples']
  assert g['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  fs={x['name']:x['features']for x in g['selected_closure']}
  assert set(['default','optimized-terminal','private-leaf-salts','program-build'])<=set(fs['aspis-r1-cost-probe'])
  assert set(['r0','pool-v1-kernel'])<=set(fs['aspis-statement']);assert 'r0' in fs['aspis-core']
  l=json.loads(pin(P/(a+'-lock-check.json')));assert l['unchanged'] and l['before']==l['after']==g['lock_sha256']
  ad=obj(P/(a+'-admission.json'));assert ad.get('exit',0)==0 and ad.get('reservation',ad).get('allowed')is True
  pair.append(r)
 assert pair[0]['source_hashes']==pair[1]['source_hashes'],i
 assert pair[0]['module']==pair[1]['module'],i
 rows.append(dict(positive=pair[0]['attempt'],control=pair[1]['attempt'],target=pair[0]['module'],identical_sources=True,semantic_control_failed=True,features=fs,source_hashes=pair[0]['source_hashes']))
# Production source byte identity; only cfg(kani) appendages in retained scratch.
for name in ['sampler.rs','transcript.rs']:
 rel='crates/aspis-r1-cost-probe/src/'+name
 frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+rel])
 assert read(R/rel)==frozen
 pin(R/rel)
(E/'NKD_NATIVE_REUSE.json').write_text(json.dumps(dict(status='PASS',pairs=rows,pinned_inputs=files,kmx_patch_sha256=sha(read(kmx)),new_solver_runs=0),indent=1)+'\n')
print('PASS: '+str(len(rows))+' native/control pairs; '+str(len(files))+' unique pinned inputs')
