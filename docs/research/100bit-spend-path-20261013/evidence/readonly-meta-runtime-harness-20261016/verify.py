#!/usr/bin/env python3
"""Verify native typecheck/source receipts; this never executes the runtime gate."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile
H=Path(__file__).resolve().parent;R=H.parents[1]
OLD='9e6384f29ce7f482d7477f9adc51d396811bbd3e';REV='b2dd7fb72bcb6395cbcc162481992e0e499204f1'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
def sha(b):return hashlib.sha256(b).hexdigest()
def load(b):return json.loads(b)
def git(rev,p):return subprocess.check_output(['git','show',rev+':'+p],cwd=R)
pin=load((H/'archive-pin.json').read_bytes());raw=(H/'runtime-harness-evidence.tar.gz').read_bytes()
assert len(raw)==pin['bytes'] and sha(raw)==pin['sha256']
manifest=load((H/'archive-members.json').read_bytes())
with tarfile.open(fileobj=io.BytesIO(raw)) as t:
 ms=t.getmembers();assert len(ms)==len(manifest)==pin['members'];assert len({m.name for m in ms})==len(ms)
 assert all(m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts for m in ms)
 def read(n):return t.extractfile(n).read()
 def js(n):return load(read(n))
 for n,p in manifest.items():
  b=read(n);assert sha(b)==p['sha256'] and len(b)==p['bytes'],n
 for label,rev,rc,inp in [('harness-check-a',OLD,101,'inputs-harness-a.json'),('harness-check-b',REV,0,'inputs.json')]:
  r=js('runs/'+label+'/receipt.json');assert r['source_revision']==rev and r['exit_status']==rc
  assert r['limits']==LIMITS and r['process_swaps']==0 and r['cgroup_swap_current']=='0'
  assert r['runner_sha256']==sha(read('run-host.py')) and r['input_manifest_sha256']==sha(read(inp))
  assert r['timeout_seconds']==600 and r['wall_seconds']<600
  cmd=r['command'];assert cmd[1:6]==['check','--release','--offline','--locked','-j1']
  assert cmd[cmd.index('--bin')+1]=='r18_replay'
  x=js(inp);assert len(x['files'])==518 and x['source_revision']==rev
  proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
  for p,h in x['files'].items():
   proc.stdin.write((rev+':'+p.removeprefix('source/')+'\n').encode());proc.stdin.flush()
   head=proc.stdout.readline().split();assert head[1]==b'blob'
   b=proc.stdout.read(int(head[2]));assert proc.stdout.read(1)==b'\n';assert sha(b)==h,p
  proc.stdin.close();assert proc.wait()==0
 assert 'non-exhaustive patterns' in read('runs/harness-check-a/stdout.log').decode()
 log=read('runs/harness-check-b/stdout.log').decode()
 assert '--crate-name r18_replay ' in log and '--emit=dep-info,metadata' in log
 assert 'Finished `release` profile' in log
 post=js('postflight.json');assert post['source_revision']==REV
 assert post['only_metadata_typecheck'] and not post['SBF_or_runtime_execution']
 assert post['all518_source_inputs_rehashed'] and post['inputs_sha256']==sha(read('inputs.json'))
 assert post['cache_binary']['unchanged_from_cache'] and post['cache_binary']['not_candidate_or_executed']
 setup=js('setup.json');assert setup['source_mtimes_refreshed_after_cache_copy'] and setup['private_copy']
 oldbinary=next(v for k,v in setup['cache_binary_and_depinfo'].items() if k.endswith('/r18_replay'))
 assert oldbinary['sha256']==post['cache_binary']['sha256']
 for row in post['checked_outputs']:
  assert sha(read(row['member']))==row['sha256'] and len(read(row['member']))==row['bytes']
 depinfo=next(read(r['member']).decode() for r in post['checked_outputs'] if r['member'].endswith('.d'))
 assert 'src/bin/r18_replay.rs' in depinfo and 'src/bin/r18_replay/readonly_runtime.rs' in depinfo
 assert len(post['actual_extern_artifacts'])==23
 for p in ['tools/r1-cost-probe/src/bin/r18_replay.rs','tools/r1-cost-probe/src/bin/r18_replay/readonly_runtime.rs','tools/r1-cost-probe/Cargo.toml','tools/r1-cost-probe/Cargo.lock']:
  assert read('source/'+p)==git(REV,p)==(R.parents[2]/p).read_bytes()
 coherent=js('final-source-coherence.json');assert coherent['source_revision']==REV and coherent['all_equal_to_extraction_pin']
 pins=load((R/'tools/readonly-meta-extraction-kit/source-pins.json').read_bytes())
 for row,orig in zip(coherent['sources'],pins['sources']):
  assert row['source']==orig['source'];b=git(REV,row['source']);assert sha(b)==row['source_sha256']
  for name,d in row['declarations'].items():
   a,z=d['span'];cut=b''.join(b.splitlines(keepends=True)[a-1:z])
   assert sha(cut)==d['sha256']==orig['declarations'][name]['sha256']
   assert cut.decode()==orig['declarations'][name]['declaration']
  assert sha(git(REV,orig['native_test_source']))==row['native_test_sha256']==orig['native_test_sha256']
 assert read('failed-source/readonly_runtime.rs')==git(OLD,'tools/r1-cost-probe/src/bin/r18_replay/readonly_runtime.rs')
 assert read('HANDOFF.txt')==(R/'design/J1-READONLY-META-RUNTIME-HANDOFF-20261016.txt').read_bytes()
 assert len(read('HANDOFF.txt').decode().split())<800
print('PASS: both retained native checks;518 combined source pins; actual rustc/dep-info/23 extern pins; metadata-only check; fixed two-copy helper coherence; runtime gate remains pending.')
