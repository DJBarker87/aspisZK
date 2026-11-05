"""Lane-owned serial validation driver, unchanged S2W host launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,tomllib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105';H='dombarker@100.108.41.90'
a=sys.argv[1];harness=sys.argv[2] if len(sys.argv)>2 else 'pair_forest_dispatch::NFO_read::association';assert __import__('re').fullmatch(r'[A-Za-z_][A-Za-z_0-9:]++',harness);assert a.startswith('NHC_K') and 1<=int(a[5:])<=120
assert not (E/a).exists() and not (E/'NHC_LEAN_ACTIVE.json').exists() and not (E/'NHC_B_LEAN_ACTIVE.json').exists()
# Reject the exact source shape of any earlier timed-out run, before admission.
for prior_patch in E.glob('NHC_K*-NHC_native.patch'):
 prior_attempt=prior_patch.name.split('-')[0]
 log=E/prior_attempt/'stdout.log'
 old_shape=E/(prior_attempt+'-shape.json')
 same_source=old_shape.exists() and __import__('re').sub(r'\s+','',json.loads(old_shape.read_text()).get('source',''))==__import__('re').sub(r'\s+','',json.loads((E/'NHC_CURRENT.json').read_text()).get('source',''))
 if log.exists() and 'CBMC timed out.' in log.read_text() and (same_source or prior_patch.read_bytes()==(E/'NHC_native.patch').read_bytes()):
  raise SystemExit('STOP unchanged timed-out shape: '+prior_attempt)
active=E/'NHC_ACTIVE.json';assert not active.exists();active.write_text(a)
sha=lambda b:hashlib.sha256(b).hexdigest()
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NHC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});q=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/{(a+'-barrier.log')!r}).read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP admission')
# Per-run equality against frozen bytes plus the sole exact scratch patch.
sys.dont_write_bytecode=True
sys.path.insert(0,str(E));from NHC_frozen_identity import frozen,apply
files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((E/'NHC_INCLUDES.json').read_text()).items()})
for p in ['NHC_KMX_copy_stubs.patch','NHC_native.patch']:apply(files,(E/p).read_text())
manifest={n:sha(v) for n,v in files.items()}
(E/(a+'-shape.json')).write_bytes((E/'NHC_CURRENT.json').read_bytes())
(E/(a+'-NHC_native.patch')).write_bytes((E/'NHC_native.patch').read_bytes())
(E/(a+'-frozen-identity.json')).write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',exact_frozen_plus_patches=True,manifest=manifest),indent=1))
closure=set(['pool-v1-kernel'])
command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NHC_src/programs/aspis-pool/Cargo.toml','--target-dir',B+'/NHC_target','--lib','--features','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']
upload={'NHC_native.patch':(E/'NHC_native.patch').read_text(),'NHC_kani_gate.py':(E/'NHC_kani_gate.py').read_text(),'NHC_RUST_SHA256.json':json.dumps(manifest),'NHC_FROZEN_GRAPH.json':(E/'NHC_FROZEN_GRAPH.json').read_text(),'NHC_KMX_copy_stubs.patch':(E/'NHC_KMX_copy_stubs.patch').read_text()}
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NHC_tmp')
cfg=dict(attempt=a,kind='kani',module=harness,command=['python3','NHC_kani_gate.py',a+'.json'],native_command=command,sources=['NHC_native.patch','NHC_kani_gate.py','NHC_RUST_SHA256.json'],env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(frozen_input_sha256=(E/'NHC_FROZEN_INPUT.json.sha256').read_text().strip(),frozen_manifest_sha256=sha((E/'NHC_FROZEN_SHA256.json').read_bytes())),program_features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit',program_manifest='programs/aspis-pool/Cargo.toml',required_statement_features=sorted(closure),expected_time='optimized compile/cache reuse, then CBMC of '+json.loads((E/'NHC_CURRENT.json').read_text()).get('kind','native local-record cut')+'; no field multiplication, hash body, or arithmetic aggregation',copy_patch_sha256=sha((E/'NHC_KMX_copy_stubs.patch').read_bytes()))
upload[a+'.json']=json.dumps(cfg)
code=f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({B!r});s=b/'NHC_src';previous=b/'NHC_applied.patch'
for n,v in json.loads({json.dumps(upload)!r}).items():(b/n).write_text(v)
for n,v in json.loads({(E/'NHC_INCLUDES.json').read_text()!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
if previous.exists():subprocess.run(['git','apply','--reverse',str(previous)],cwd=s,check=True,capture_output=True)
subprocess.run(['git','apply',str(b/'NHC_native.patch')],cwd=s,check=True,capture_output=True)
previous.write_text((b/'NHC_native.patch').read_text())
expected=json.loads((b/'NHC_RUST_SHA256.json').read_text())
assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in expected.items()),'STOP frozen mismatch'
'''
r=ssh('python3',code);(E/(a+'-upload.log')).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-source-check.json',a+'-tools.json',a+'-metadata-pin.json',a+'-metadata.stderr',a+'-graph-check.json',a+'-lock-check.json',a+'-rule16-check.json',a+'-temp-files.json']!r}
out={{n:(b/n).read_text() for n in names if (b/n).exists()}}
cleaned=[]
if (b/{(a+'/receipt.json')!r}).exists():
 for pattern in ['external-sat*','smt2_dec_problem*']:
  for p in (b/'NHC_tmp').rglob(pattern):
   if p.is_file():cleaned.append(dict(path=str(p),size=p.stat().st_size));p.unlink()
 out[{(a+'-solver-cleanup.json')!r}]=json.dumps(dict(terminal_attempt={a!r},removed=cleaned))
print(json.dumps(out))
'''
for recovery_retry in range(11):
 r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
 for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 if a+'/receipt.json' in out:break
 with (E/'NHC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,recovery_retry=recovery_retry,action='read-only wait for terminal receipt; never resubmit'))+'\n')
 if recovery_retry<10:time.sleep(60)
assert a+'/receipt.json' in out,'unresolved submitted attempt; never resubmit'
rc=json.loads(out[a+'/receipt.json']);entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
with (E/'NHC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
# Budget ledger is checked independently; no historical checkpoint mutation.
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print('Terminal stdout retained in receipt directory; source excerpts suppressed.');sys.exit(rc['exit_status'])
