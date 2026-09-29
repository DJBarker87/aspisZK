#!/usr/bin/env python3
"""Tiny offline Nat-only fallback; no cold dependency or full-runtime build.
Lean heap cap 1024 MiB, one worker, per-command CPU limit 30s/35s and wall 60s.
Run only with the already compiled pinned macOS Lean/mathlib cache.
"""
import argparse, hashlib, json, os, resource, shutil, signal, subprocess, tempfile
from pathlib import Path

root=Path(__file__).resolve().parent.parent
p=argparse.ArgumentParser();p.add_argument('--reuse',type=Path);a=p.parse_args()
sources=root/'lean'
retained=Path('/Users/dominic/ZK/AspisFormal')
packages=retained/'.lake/packages'
expected='81a5d257c8e410db227a6665ed08f64fea08e997'
assert subprocess.check_output(['git','-C',str(packages/'mathlib'),'rev-parse','HEAD'],text=True).strip()==expected
assert (retained/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.0'
assert (packages/'mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Notation.olean').is_file()
out=Path(tempfile.mkdtemp(prefix='aspis-r64-local-bound-'));cache=out/'lib';cache.mkdir()
workspace=out/'workspace';workspace.mkdir()
(workspace/'lakefile.toml').write_text('name = "r64_local_bound"\nversion = "0.0.0"\n')
(workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
deps=sorted(packages.glob('*/.lake/build/lib/lean'))
env=dict(os.environ,PATH='/Users/dominic/.elan/bin:/usr/bin:/bin',NO_DNA='1',
    LEAN_PATH=':'.join(map(str,[cache,*deps])))
def limits():resource.setrlimit(resource.RLIMIT_CPU,(30,35))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
old=json.loads((a.reuse/'metadata.json').read_text()) if a.reuse else []
for target in ['AspisV8R17/RawReducerNat','AspisV8R19/CanonicalProduct']:
    src=sources/(target+'.lean');obj=cache/(target+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    found=next((r for r in old if r['target_name']==target and r['exit']==0 and r['source_sha256']==sha(src)),None)
    if found:
        assert found['toolchain']=='leanprover/lean4:v4.32.0' and found['mathlib_revision']==expected
        for f in (a.reuse/'lib'/target).parent.glob(Path(target).name+'.*'):shutil.copy2(f,obj.parent/f.name)
        shutil.copy2(a.reuse/(Path(target).name+'.log'),out/(Path(target).name+'.log'))
        records.append(found);continue
    cmd=['/Users/dominic/.elan/bin/lake','env','lean','-j1','-M1024','-R',str(sources),'-o',str(obj),str(src)]
    log=out/(Path(target).name+'.log')
    with log.open('w') as f:
        process=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=workspace,env=env,
            stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
        try:code=process.wait(timeout=60)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=5);code=124
    records.append({'target_name':target,'source_sha256':sha(src),'exit':code,'command':cmd,
      'base_revision':'2a9d914ff615bfc9d046399074d05b8164791412',
      'toolchain':'leanprover/lean4:v4.32.0','mathlib_revision':expected,
      'lean_heap_mib':1024,'cpu_soft_seconds':30,'cpu_hard_seconds':35,'wall_limit_seconds':60,
      'source_change_or_replay_reason':'missing local compiled object and first focused proof check'})
    (out/'metadata.json').write_text(json.dumps(records,indent=2)+'\n')
    print(log.read_text(),flush=True)
    print(json.dumps({'output':str(out),'target':target,'exit':code}),flush=True)
    if code:raise SystemExit(code)
    assert 'sorryAx' not in log.read_text()
