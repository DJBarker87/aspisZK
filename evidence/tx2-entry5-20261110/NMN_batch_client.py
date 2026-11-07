from NMN_formal import *
import difflib,base64

def batch(scope,jobs):
 rows=[json.loads(l) for l in (E/'NMN_ATTEMPTS.jsonl').read_text().splitlines()]
 assert sum(x['kind']=='kani' for x in rows)+len(jobs)<=80
 for job in jobs:
  assert not (E/job['attempt']).exists()
 lib='programs/r1-cost-probe/src/lib.rs';owned='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
 get=lambda n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 files={'NMN_src/'+lib:'#![cfg_attr(kani,feature(allocator_api))]\n'+get(lib),'NMN_src/'+owned:get(owned)+'\n#[cfg(kani)]\n#[path="NMN_program.rs"]\nmod NMN_program;\n'}
 for n in ['NMN_program.rs','NMN_heap.rs','NMN_statement.rs']:files['NMN_src/programs/r1-cost-probe/src/'+n]=(E/n).read_text()
 files['NMN_gate.py']=(E/'NMN_gate.py').read_text();files['NMN_program_batch.py']=(E/'NMN_program_batch.py').read_text()
 manifest={'scope':scope,'jobs':[]}
 for job in jobs:
  target='r1_pool_adapter::owned::NMN_program::'+job['target']
  cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMN_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMN_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
  manifest['jobs'].append(dict(**{**job,'target':target},config=dict(attempt=job['attempt'],native_command=cmd,root_package='aspis-r1-cost-probe-program')))
 files[scope+'-manifest.json']=json.dumps(manifest,indent=1)+'\n'
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 parent=run(scope,'batch','sequential native variants',['python3','NMN_program_batch.py',scope+'-manifest.json'],files,env)
 r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});out={{}}
for p in (b/'NMN_batch'/{scope!r}).glob('*'):
 if p.is_file():out[str(p.relative_to(b))]=base64.b64encode(p.read_bytes()).decode()
for a in {[x['attempt'] for x in jobs]!r}:
 for pat in [a+'-graph*',a+'-source*',a+'-lock*',a+'-kani-submitted.json',a+'-native-config.json']:
  for p in b.glob(pat):
   if p.is_file():out[str(p.relative_to(b))]=base64.b64encode(p.read_bytes()).decode()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
 for name,data in json.loads(r.stdout).items():
  raw=base64.b64decode(data);p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
  if name.endswith('.log'):
   p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
  else:p.write_bytes(raw)
 for job in jobs:
  p=E/'NMN_batch'/scope/(job['attempt']+'.receipt.json')
  if not p.exists():continue
  rc=json.loads(p.read_text());rc.update(source_revision=parent['source_revision'],source_hashes=parent['source_hashes'],limits=parent['limits'],cgroup=parent['cgroup'],deps_fingerprint=parent['deps_fingerprint'],parent_scope_receipt=scope+'/receipt.json')
  d=E/job['attempt'];d.mkdir(exist_ok=True);(d/'receipt.json').write_text(json.dumps(rc,indent=1)+'\n')
  summary={k:v for k,v in rc.items() if k!='deps_fingerprint'};summary['full_receipt']=job['attempt']+'/receipt.json'
  with (E/'NMN_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
 return parent
if __name__=='__main__':
 x=json.loads((E/sys.argv[1]).read_text());batch(x['scope'],x['jobs'])
