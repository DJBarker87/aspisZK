#!/usr/bin/env python3
"""Read/hash evidence verification only; no compiler, prover, SBF or runtime job."""
from pathlib import Path
import hashlib,io,json,re,subprocess,tarfile,tomllib
H=Path(__file__).resolve().parent;R=H.parents[1]
REV='20672afeffd5757f8f8eb024a71a1ce86001c7e2'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def digest(x):return sha(json.dumps(x,sort_keys=True).encode())
def load(b):return json.loads(b)
def git(p):return subprocess.check_output(['git','show',REV+':'+p],cwd=R)
pin=load((H/'archive-pin.json').read_bytes());raw=(H/'readonly-meta-evidence.tar.gz').read_bytes()
assert len(raw)==pin['bytes'] and sha(raw)==pin['sha256']
members=load((H/'archive-members.json').read_bytes())
with tarfile.open(fileobj=io.BytesIO(raw)) as t:
 ms=t.getmembers();assert len(ms)==len(members)==pin['members']
 assert len({m.name for m in ms})==len(ms)
 assert all(m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts for m in ms)
 def read(n):return t.extractfile(n).read()
 def js(n):return load(read(n))
 for n,p in members.items():
  b=read(n);assert len(b)==p['bytes'] and sha(b)==p['sha256'],n
 sp=js('extraction/input/source-pins.json');assert sp['source_revision']==REV
 hs=[];ws=[];tests=[]
 for row in sp['sources']:
  b=git(row['source']);assert sha(b)==row['source_sha256']
  for name,store in [('readonly_meta_ok',hs),('require_readonly_account',ws)]:
   p=row['declarations'][name];a,z=p['span'];cut=b''.join(b.splitlines(keepends=True)[a-1:z])
   assert cut.decode()==p['declaration'] and sha(cut)==p['sha256'];store.append(cut)
  b=git(row['native_test_source']);assert sha(b)==row['native_test_sha256'];tests.append(b)
 assert hs[0]==hs[1] and ws[0]==ws[1] and tests[0]==tests[1]
 assert sp['identical_helpers'] and sp['identical_wrappers'] and sp['identical_native_tests']
 kit=R/'tools/readonly-meta-extraction-kit'
 for n in [*sp['kit_files'],'source-pins.json','Cargo.lock']:
  assert read('extraction/input/'+n)==(kit/n).read_bytes(),n
 for n,h in sp['kit_files'].items():assert sha(read('extraction/input/'+n))==h
 assert read('extraction/Cargo.lock.seed')==git('Cargo.lock')
 native=js('native/inputs.json');old=js('native/inputs-original.json')
 assert native['source_revision']==old['source_revision']==REV
 assert len(native['files'])==509 and len(old['files'])==508
 assert all(native['files'][p]==h for p,h in old['files'].items())
 # Check every staged native project file against the producing Git revision.
 process=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for p,h in native['files'].items():
  b=read('native/'+p);assert sha(b)==h
  process.stdin.write((REV+':'+p.removeprefix('source/')+'\n').encode());process.stdin.flush()
  header=process.stdout.readline().split();assert header[1]==b'blob'
  actual=process.stdout.read(int(header[2]));assert process.stdout.read(1)==b'\n';assert actual==b,p
 process.stdin.close();assert process.wait()==0
 for label,rc in [('probe-tests-a',0),('verifier-tests-a',101),('verifier-tests-b',0)]:
  r=js('native/runs/'+label+'/receipt.json');assert r['exit_status']==rc and r['source_revision']==REV
  assert r['limits']==LIMITS and r['process_swaps']==0 and r['cgroup_swap_current']=='0'
  assert r['runner_sha256']==sha(read('native/run-host.py'))
  expected='native/inputs.json' if label.endswith('-b') else 'native/inputs-original.json'
  assert r['input_manifest_sha256']==sha(read(expected))
  log=read('native/runs/'+label+'/stdout.log').decode()
  if rc==0:assert '5 passed; 0 failed' in log
  else:assert 'v7-proof.bin' in log and 'No such file or directory' in log
 seed=tomllib.loads(read('extraction/Cargo.lock.seed').decode())['package']
 selected=tomllib.loads(read('extraction/input/Cargo.lock').decode())['package']
 seedmap={(r['name'],r['version'],r.get('source')):r for r in seed}
 for r in selected:
  if r.get('source'):assert seedmap[(r['name'],r['version'],r['source'])]['checksum']==r['checksum']
 dep=js('extraction/dependency-audit.json');assert dep['source_revision']==REV
 assert dep['selected_lock_sha256']==sha(read('extraction/input/Cargo.lock'))
 assert dep['metadata_sha256']==sha(read('extraction/runs/metadata-a/stdout.log'))
 assert len(dep['packages'])==62 and dep['verified_source_files']==1839
 crates={(r['name'],r['version']):r for r in js('registry-archives.json')};assert len(crates)==65
 for key,r in crates.items():
  assert sha(read(r['member']))==r['checksum']==r['sha256']
  assert next(s for s in seed if (s['name'],s['version'])==key)['checksum']==r['checksum']
 count=0
 for r in js('registry-source-file-audit.json'):
  c=crates[(r['name'],r['version'])];assert c['selected'];assert c['checksum']==r['archive_sha256']
  with tarfile.open(fileobj=io.BytesIO(read(c['member']))) as ct:
   found={};prefix=r['name']+'-'+r['version']
   for m in ct.getmembers():
    if m.isfile():
     b=ct.extractfile(m).read();found[str(Path(m.name).relative_to(prefix))]={'bytes':len(b),'sha256':sha(b)}
   assert found==r['files'];count+=len(found)
 assert count==1839
 for r in js('source-files.json'):
  assert sha(read(r['member']))==r['sha256']
  if r['member'].startswith('source-files/registry/'):
   rel=str(Path(r['member']).relative_to('source-files/registry'));prefix=rel.split('/')[0]
   c=next(r for r in crates.values() if r['name']+'-'+r['version']==prefix)
   with tarfile.open(fileobj=io.BytesIO(read(c['member']))) as ct:assert ct.extractfile(rel).read()==read(r['member'])
 llbc=js('extraction/ReadonlyMeta.llbc');tr=llbc['translated'];inv=js('llbc-inventory.json')
 assert not llbc['has_errors'] and llbc['charon_version']=='0.1.223'
 assert inv['llbc_sha256']==sha(read('extraction/ReadonlyMeta.llbc'))
 assert tr['fun_decls'][0]['item_meta']['source_text']==hs[0].decode().rstrip('\n')
 assert len(tr['type_decls'][2]['kind']['Enum'])==26
 assert inv['error_nodes']==[] and len(inv['opaque_or_foreign'])==16
 assert set(inv['generated_files'])=={'translation.json','AspisR1ReadonlyMeta/Types.lean','AspisR1ReadonlyMeta/Funs.lean'}
 for n in ['Types','Funs']:
  b=read('extraction/generated/AspisR1ReadonlyMeta/'+n+'.lean')
  assert b==(R/'lean/extracted-readonly-meta-20261016/AspisR1ReadonlyMeta'/(n+'.lean')).read_bytes()
  assert b==read('proofs/sources/AspisR1ReadonlyMeta/'+n+'.lean')
 for label in ['metadata-a','charon-a','aeneas-a']:
  r=js('extraction/runs/'+label+'/receipt.json');assert r['exit_status']==0 and r['source_revision']==REV
  assert r['limits']==LIMITS and r['swaps']==0 and r['wall_seconds']<180
  assert r['runner_sha256']==sha(read('extraction/run-host.py'))
 tool=js('extraction/tool-pins.json');ret=load((H.parent/'native-r18-tools-20261016/tools-final-pins.json').read_bytes())
 assert all(ret[k]==v for k,v in tool.items()) and js('final-runtime-recheck.json')['all_match']
 assert js('final-runtime-recheck.json')['tool_pins_sha256']==sha(read('extraction/tool-pins.json'))
 manifest=js('proofs/sources/SOURCE-MANIFEST.json');receipts={};audits=0
 external=js('proofs/runs/generated-a/external-inputs.json');keys={}
 def ekey(n):
  if n in keys:return keys[n]
  row=external['modules'][n]
  k={'source':row['source_sha256'],'objects':{s:o['sha256'] for s,o in row['objects'].items()},'imports':{d:ekey(d) for d in row['imports']},'runtime':external['runtime_files']}
  keys[n]=digest(k);return keys[n]
 for n in manifest['topological_order']:
  item=manifest['modules'][n]
  s=read('proofs/sources/'+item['stage_as']);assert sha(s)==item['source_sha256']
  assert s==(R.parents[2]/item['source']).read_bytes(),item['source']
  r=js('proofs/successful-targets/'+n+'.json');receipts[n]=r
  assert r['exit_status']==0 and r['axioms']['passed'] and r['limits']==LIMITS
  assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
  assert r['key']['source_sha256']==sha(s) and r['key']['runtime']==external['runtime_files']
  assert r['key']['options']==['-j1','-M0']
  assert len(r['axioms']['reports'])==item['axiom_requests'];audits+=item['axiom_requests']
  assert all(set(a['axioms'])<=STANDARD for a in r['axioms']['reports'])
  for suffix,p in r['objects'].items():assert sha(read('proofs/objects/'+n.replace('.','/')+suffix))==p['sha256']
  expected={}
  for d in ['Init',*item['imports']]:
   if d in receipts:expected[d]={'objects':receipts[d]['objects'],'receipt_key':digest(receipts[d]['key'])}
   else:expected[d]={'objects':external['modules'][d]['objects'],'closure_key':ekey(d)}
  assert r['key']['imports']==expected,n
 assert len(receipts)==5 and audits==8
 assert read('REPORT.txt')==(R/'design/J1-READONLY-META-20261016.txt').read_bytes()
 assert len(read('REPORT.txt').decode().split())<800
 assert js('check-summary.json')==load((H/'check-summary.json').read_bytes())
print('PASS: exact two-copy helper/wrapper/tests;509 native source pins;65 registry archives/1839 files; native5+5; exact SDK extraction;5 Lean targets/8 standard-only audits; conditional R16 boundary only.')
