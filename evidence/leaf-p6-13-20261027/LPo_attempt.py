"""Configure the unchanged admitted S2W runner; one proof scope per invocation."""
from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027'
a,kind,target=sys.argv[1:]
limit=30 if kind=='kani' else 80
if int(a.rsplit('_',1)[1][1:])>limit:raise SystemExit('STOP exhausted budget')
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def collect(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
if (E/a/'receipt.json').exists():raise SystemExit('Refuse existing attempt')
# Own launch guard: never admit a second proof while an older attempt lacks
# its terminal receipt. Source writing/read-only work can proceed separately.
for existing in E.glob('LPo_[LK][0-9][0-9][0-9].json'):
 name=existing.stem
 if name!=a and not (E/name/'receipt.json').exists():
  raise SystemExit('STOP own attempt still active or needs receipt: '+name)
remote=ssh("pgrep -af '^(/usr/bin/)?python3 S2W_(run|lean)_host.py LPo_' || true")
if remote.stdout.strip():raise SystemExit('STOP own host proof active: '+remote.stdout)
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');collect(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  collect(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:print(a,'reservation wait',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP reservation retries')
(E/(a+'-admission.json')).write_text(json.dumps({'exit_status':r.returncode,'allowed':ad['allowed'],'retry':retry})+'\n')
cfg=dict(attempt=a,kind=kind,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,reservation_retries=retry)
if kind=='kani':
 cfg.update(sources=['LPo_src/Cargo.toml','LPo_src/Cargo.lock']+['LPo_src/'+p for p in json.loads((E/'LPo_sources.json').read_text())],command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/LPo_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/LPo_target','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse'],deps_fingerprint={'release_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_manifest':'LPo_source-provenance.json','boundary':'scratch frozen source plus ordered LPa/LPc/LPg/LPh/LPl then LPn cfg-only patches'},expected_time='optimized Kani compilation then bounded native stage '+target,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1','TMPDIR':B+'/LPo_tmp'})
else:
 src='LPo_generated/'+target+'.lean';obj='LPo_objects/'+target+'.olean'
 cfg['kind']='lean'
 cfg.update(module=target,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','LPo_generated','-o',obj,src],env={'LEAN_PATH':B+'/LPo_objects:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'},deps_fingerprint={'scope':'coherent SInt2 objects plus LPl new modules'},expected_time='single symbolic module; no concrete large numeral normalization')
 r=ssh(f'mkdir -p {B}/LPo_generated {B}/LPo_objects');assert r.returncode==0,r.stderr
 if kind == 'replay':
  R='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/'
  cfg['env']['LEAN_PATH']=B+'/LPo_objects:'+':'.join(R+x for x in ['RPv_overlay','RPu_overlay','RPt_overlay','RPz8_overlay','RPz7_overlay','RPz4_trusted','RPz_trusted'])
 if kind=='inherited':
  local=Path(next(x['repository_source'] for x in json.loads((E/'LPo_inherited-plan.json').read_text()) if x['module']==target))
  r=ssh(f'mkdir -p {B}/LPo_inherited/'+str(Path(target.replace(".","/")).parent));assert r.returncode==0,r.stderr
  subprocess.run(['scp','-q',str(local),H+':'+B+'/'+src],check=True)
 if kind!='inherited':subprocess.run(['scp','-q',str((Path('lean') if kind=='dependency' else Path('evidence/leaf-p6-10-20261027') if kind=='reuse' else E)/(target+'.lean')),H+':'+B+'/'+src],check=True)
pins=ssh("python3 - <<'PIN'\nfrom pathlib import Path\nimport hashlib,json\nr=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')\nps=[r/'Aeneas.olean']+list((r/'Aeneas').rglob('*.olean'))+list((r/'AeneasMeta').rglob('*.olean'))\nprint(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ps)}))\nPIN")
assert pins.returncode==0,pins.stderr
cfg['deps_fingerprint']['aeneas_library_objects']=json.loads(pins.stdout)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
if kind=='kani' and (a=='LPo_K029' or a=='LPo_K030'):
 cfg['command'][cfg['command'].index('terse')]='old'
 cfg['command']+=['--cbmc-args','--trace']
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
if kind=='kani':
 r=ssh(f'mkdir -p {B}/LPo_tmp');assert r.returncode==0,r.stderr
 import LPo_graph
 LPo_graph.check(a)
 for name in ['LPo_harness.patch']:
  subprocess.run(['scp','-q',H+':'+B+'/'+name,str(E/(a+'-harness.patch'))],check=True)
 import hashlib
 patch=E/(a+'-harness.patch')
 (E/(a+'-patch.json')).write_text(json.dumps({'sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),'base':'read-only LPl_src final source tree'})+'\n')
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 {('S2W_run_host.py' if kind=='kani' else 'S2W_lean_host.py')} {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
if kind=='kani':
 post=ssh(f'sha256sum {B}/LPo_src/Cargo.lock')
 (E/(a+'-lock-after.log')).write_text(post.stdout+post.stderr)
 if post.returncode or post.stdout.split()[0]!='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef':raise SystemExit('STOP lock drift')
for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
if kind!='kani':
 local=Path(next(x['repository_source'] for x in json.loads((E/'LPo_inherited-plan.json').read_text()) if x['module']==target)) if kind=='inherited' else (Path('lean') if kind=='dependency' else Path('evidence/leaf-p6-10-20261027') if kind=='reuse' else E)/(target+'.lean')
 (E/a/'source.lean.txt').write_bytes(local.read_bytes())
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms']}),flush=True)
print((E/a/'stdout.log').read_text()[-1500:],flush=True)
