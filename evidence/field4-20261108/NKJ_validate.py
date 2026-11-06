from pathlib import Path
import json,hashlib,lzma,copy,shlex,re,subprocess
E=Path(__file__).resolve().parent
FROZEN='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def receipt(n):return json.loads((E/f'NKJ_K{n:03}'/'receipt.json').read_text())
def kani_valid(r,g,l,positive):
 assert r['limits']==LIMITS and r['env']['CARGO_NET_OFFLINE']=='true'
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-field4-20261108/NKJ_target'
 assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert g['graph_matches_frozen'] and g['lock_sha256']==FROZEN
 assert l['unchanged'] and l['before']==l['after']==FROZEN
 assert r['exit_status']==0 if positive else r['exit_status']!=0
 assert next(x for x in g['selected_closure'] if x['name']=='aspis-core')['features']==['r0']
def pair(p,n):
 a,b=receipt(p),receipt(n)
 for r,positive in [(a,True),(b,False)]:
  at=r['attempt'];g=json.loads((E/(at+'-graph-check.json')).read_text());l=json.loads((E/(at+'-lock-check.json')).read_text())
  kani_valid(r,g,l,positive)
  log=(E/at/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in log
  if not positive:assert 'Failed Checks:' in log
  assert not json.loads((E/(at+'-source-check.json')).read_text())['errors']
  ad=json.loads((E/(at+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert a['native_command']==b['native_command']
 assert a['source_hashes']['NKJ_segments.rs.txt']==b['source_hashes']['NKJ_segments.rs.txt']
 env=dict(b['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg NKJ_invert','')
 assert env==a['env'] and b['env']['RUSTFLAGS'].count(' --cfg NKJ_invert')==1
PAIRS=[(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(27,28),(29,30),(31,32),(33,34),(35,36),(56,57),(63,64)]
FAMILIES=[(17,18,19,20,21),(22,23,24,25,26),(37,38,39,40,41),(58,59,60,61,62),(65,66,67,68,69)]
def validate_native():
 for p,n in PAIRS:pair(p,n)
 for weak,inv,real,unimplied,modifies in FAMILIES:
  pair(weak,inv)
  assert len({receipt(n)['source_hashes']['NKJ_segments.rs.txt'] for n in [weak,inv,real,unimplied,modifies]})==1
  for n,positive,needle in [(real,True,'VERIFICATION:- SUCCESSFUL'),(unimplied,False,'Failed Checks:'),(modifies,False,'is assignable')]:
   r=receipt(n);a=r['attempt'];kani_valid(r,json.loads((E/(a+'-graph-check.json')).read_text()),json.loads((E/(a+'-lock-check.json')).read_text()),positive)
   assert needle in (E/a/'stdout.log').read_text()
 assert sha(E/'NKJ_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for a,pins in json.loads((E/'NKJ_INHERITED_NATIVE_PINS.json').read_text()).items():
  for n,x in pins.items():assert sha(Path(n))==x['sha256']
def validate_audit():
 f=json.loads((E/'NKJ_audit/fixtures.json').read_text());p=json.loads((E/'NKJ_audit/proof2.json').read_text());s=json.loads((E/'NKJ_audit/scan_summary.json').read_text())
 assert f['exit']==p['exit']==0 and not f['errors'] and not p['errors'] and not s['errors']
 assert f['binary_sha256']==p['binary_sha256']
 assert len(f['roots'])==8
 roots=json.loads((E/'NKJ_AUDIT_ROOTS.json').read_text());assert sorted(roots)==sorted(r['root'] for r in p['roots'])
 for r in p['roots']:assert r['equal'] and set(r['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
 for a in ['NKJ_L033','NKJ_L034','NKJ_L035']:
  r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['limits']==LIMITS
 # Every successful owned theorem source must agree with its latest successful compile.
 compiled={}
 for pth in sorted(E.glob('NKJ_L[0-9][0-9][0-9]/receipt.json')):
  r=json.loads(pth.read_text())
  if r['kind']=='lean' and r['exit_status']==0:
   for n,h in r['source_hashes'].items():
    if n.endswith('.lean'):compiled[n]=h
 for n,h in compiled.items():assert sha(E/n)==h,(n,'source changed after successful compile')
 for pth in E.rglob('*.sha256'):
  raw=pth.with_suffix('');compressed=Path(str(raw)+'.xz')
  if compressed.exists():assert hashlib.sha256(lzma.decompress(compressed.read_bytes())).hexdigest()==pth.read_text().strip()
def mutations():
 r=receipt(5);g=json.loads((E/'NKJ_K005-graph-check.json').read_text());l=json.loads((E/'NKJ_K005-lock-check.json').read_text())
 cases=[]
 for path,value in [('exit_status',1),('env.CARGO_NET_OFFLINE','false'),('env.CARGO_TARGET_DIR','/tmp/other'),('env.CARGO_PROFILE_DEV_OPT_LEVEL','0'),('limits.memory.max','17179869184')]:
  c=copy.deepcopy(r);top,sep,key=path.partition('.')
  if sep:c[top][key]=value
  else:c[top]=value
  cases.append((c,g,l))
 c=copy.deepcopy(g);c['graph_matches_frozen']=False;cases.append((r,c,l))
 c=copy.deepcopy(l);c['after']='0'*64;cases.append((r,g,c))
 for args in cases:
  try:kani_valid(*args,True)
  except AssertionError:continue
  raise AssertionError('counterfactual admitted')
 return len(cases)
if __name__=='__main__':
 validate_native();validate_audit();count=mutations()
 print(json.dumps(dict(native_pairs=len(PAIRS),shape_families=len(FAMILIES),counterfactuals_rejected=count,status='PASS')))
