"""Own validation wrapper; immutable S2W backend; one scoped native run."""
from pathlib import Path
import subprocess,sys,json,time,shlex,hashlib,tomllib,zlib,base64
from NBS_expected import expected
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028';S=B+'/NBS_src'
a,crate,harness=sys.argv[1:4]
extra=Path(sys.argv[4]) if len(sys.argv)>4 else None
assert len(list(E.glob('NBS_K*/receipt.json')))<40
assert len(list(E.glob('NBS_L*/receipt.json')))<100
assert not (E/a/'receipt.json').exists()
def ssh(code,submitted=False,stdin=None):
 args=['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code]
 for n in range(11):
  r=subprocess.run(args,capture_output=True,text=True,input=stdin)
  with (E/'NBS_K_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=submitted))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else '{{}}');sys.exit(r.returncode)
'''
 r=ssh('python3 -c '+shlex.quote(code));(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 ad=json.loads(r.stdout or '{}');(E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if not ad and retry==0:time.sleep(30);continue
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation refused; wait180s',flush=True);time.sleep(180);continue
 raise SystemExit('STOP admission error')
request=Path(sys.argv[4]);patch=request.read_text();validated=expected(request)
(E/(a+'-source-check.json')).write_text(json.dumps(validated,indent=2)+'\n')
source_blob=base64.b64encode(zlib.compress(json.dumps(validated).encode())).decode()
extra=None
setup=f'''from pathlib import Path
import subprocess,hashlib,json
b=Path({B!r});s=Path({S!r})
launchers=json.loads({(E/'NBS_LAUNCHER_INPUTS.json').read_text()!r})
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 q=b/n;t=launchers[n]
 if q.exists():assert q.read_text()==t,(n,'backend differs')
 else:q.write_text(t)
p=b/{(a+'-harness.patch')!r}
patch={patch!r}
if p.exists():assert p.read_text()==patch,'scratch patch changed'
else:p.write_text(patch)
import zlib,base64
validation=json.loads(zlib.decompress(base64.b64decode({source_blob!r})))
def drift(expected):return [name for name,h in expected.items() if not (s/name).is_file() or hashlib.sha256((s/name).read_bytes()).hexdigest()!=h]
already=not drift(validation['after'])
assert already or not drift(validation['before']),('scratch before-image drift',drift(validation['before']))
if validation['apply'] and not already:
 r=subprocess.run(['git','apply',str(p)],cwd=s,capture_output=True,text=True)
 assert r.returncode==0,r.stdout+r.stderr
assert not drift(validation['after']),('scratch after-image drift',drift(validation['after']))
print(hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest())
'''
r=ssh('python3',stdin=setup);assert r.returncode==0,r.stdout+r.stderr
if extra:
 extension=extra.read_text()
 code=f'''from pathlib import Path
import subprocess
b=Path({B!r});s=Path({S!r})
launchers=json.loads({(E/'NBS_LAUNCHER_INPUTS.json').read_text()!r})
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 q=b/n;t=launchers[n]
 if q.exists():assert q.read_text()==t,(n,'backend differs')
 else:q.write_text(t)
p=b/{extra.name!r}
assert not p.exists(),'do not reapply an extension'
p.write_text({extension!r})
r=subprocess.run(['git','apply',str(p)],cwd=s,capture_output=True,text=True)
assert r.returncode==0,r.stdout+r.stderr
'''
 q=ssh('python3 -c '+shlex.quote(code));assert q.returncode==0,q.stdout+q.stderr
 (E/(a+'-extra.patch')).write_text(extension)
(E/(a+'-harness.patch')).write_text(patch)
locksha=hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
(E/(a+'-lock-before.log')).write_text(r.stdout+r.stderr);assert r.stdout.strip()==locksha
r=ssh('cd '+shlex.quote(S)+' && CARGO_NET_OFFLINE=true /home/dombarker/.cargo/bin/cargo metadata --locked --offline --format-version 1')
(E/(a+'-graph.stderr')).write_text(r.stderr);assert r.returncode==0,r.stderr
# Parse the single JSON object independently of any preceding diagnostics.
m=next(json.loads(line) for line in r.stdout.splitlines() if line.startswith('{'))
frozen=tomllib.loads(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock']).decode())
key=lambda p:(p['name'],p['version'],p.get('source'))
f={key(p):p for p in frozen['package']};actual={key(p):p for p in m['packages']}
nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']}
added=sorted(set(actual)-set(f),key=str);errors=[]
assert not added,added
for p in m['packages']:
 for dep in nodes[p['id']]['dependencies']:
  q=pkgs[dep]
  if not any((bits:=label.split(' '))[0]==q['name'] and (len(bits)>1 or sum(k[0]==q['name'] for k in f)==1) and (len(bits)<2 or bits[1]==q['version']) and (len(bits)<3 or bits[2].strip('()')==q.get('source')) for label in f[key(p)].get('dependencies',[])):errors.append([key(p),key(q)])
graph=dict(resolved_packages=len(actual),new_package_tuples=added,edge_errors=errors,graph_matches_frozen=not added and not errors,graph_sha256=hashlib.sha256(json.dumps(m,sort_keys=True).encode()).hexdigest(),lock_sha256=locksha)
(E/(a+'-graph-check.json')).write_text(json.dumps(graph,indent=2)+'\n');assert graph['graph_matches_frozen']
frozen_sources=json.loads((E.parent/'native-tx2h-20261028/NBQ_SCRATCH_MANIFEST.json').read_text())
modified=sorted(name for name,h in validated['after'].items() if frozen_sources.get(name)!=h)
cfg=dict(attempt=a,kind='kani',timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,reservation_retries=retry,sources=['NBS_src/'+p for p in ['Cargo.toml','Cargo.lock']+modified],command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',S+'/'+crate+'/Cargo.toml','--target-dir',B+'/NBS_target','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse'],env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1','TMPDIR':B+'/NBS_tmp'},deps_fingerprint={'frozen_source':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph':graph,'harness_patch_sha256':hashlib.sha256(patch.encode()).hexdigest(),'extra_patch_sha256':hashlib.sha256(extension.encode()).hexdigest() if extra else None,'scratch_source_manifest_sha256':hashlib.sha256(json.dumps(validated['after'],sort_keys=True).encode()).hexdigest(),'cfg_patch_chain':validated['patch_chain']},expected_time='optimized dependency compilation then native release leaf '+harness)
if crate.startswith('programs/'):
 cfg['command']+=['--features','pool-adapter,private-leaf-salts']
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
code=f'''from pathlib import Path
import json
b=Path({B!r});(b/'NBS_tmp').mkdir(exist_ok=True)
(b/{(a+'.json')!r}).write_text({json.dumps(cfg,indent=2)!r})
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
# Submission is never repeated; post-submission transport failures recover read-only.
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=Path({S!r})
names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r}]
print(json.dumps(dict(files={{n:(b/n).read_text() for n in names if (b/n).is_file()}},lock_after=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest())))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/(a+'-lock-after.log')).write_text(out['lock_after']+'\n');assert out['lock_after']==locksha,'STOP lock drift'
for n,t in out['files'].items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
assert a+'/receipt.json' in out['files'],'STOP missing submitted receipt'
rc=json.loads(out['files'][a+'/receipt.json']);print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print(out['files'][a+'/stdout.log'][-6000:])
