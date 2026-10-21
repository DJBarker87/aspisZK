#!/usr/bin/env python3
"""Isolated source sampler reproduction; no shipped source mutation or SBF build."""
import hashlib, json, pathlib, shlex, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[4]
HERE = pathlib.Path(__file__).resolve().parent
HOST = 'dombarker@100.108.41.90'
REMOTE = '/home/dombarker/project-offloads/codex-cx-ser-join-20261021'

def ssh(script):
    return subprocess.check_output(['ssh', '-o', 'ServerAliveInterval=30', '-o', 'ServerAliveCountMax=3', HOST, script], text=True, timeout=1200)

ssh('mkdir -p '+REMOTE+'/source/crates/aspis-core '+REMOTE+'/source/probe/src')
subprocess.run(['rsync', '-a', str(ROOT/'crates/aspis-core/src')+'/', HOST+':'+REMOTE+'/source/crates/aspis-core/src/'], check=True)
subprocess.run(['scp', str(ROOT/'crates/aspis-core/Cargo.toml'), str(ROOT/'crates/aspis-core/build.rs'), HOST+':'+REMOTE+'/source/crates/aspis-core/'], check=True)
subprocess.run(['scp', str(HERE/'ser-join-sampler-probe.rs'), HOST+':'+REMOTE+'/source/probe/src/main.rs'], check=True)
manifest = '''[workspace]
members = ["crates/aspis-core", "probe"]
resolver = "2"
[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
version = "0.1.0"
'''
probe_manifest = '''[package]
name = "aspis-ser-join-probe"
version = "0.1.0"
edition = "2021"
[dependencies]
aspis-core = { path = "../crates/aspis-core" }
'''
script = '''import pathlib,subprocess,json,os,time
R=pathlib.Path(REMOTE)
(R/'source/Cargo.toml').write_text(MANIFEST)
(R/'source/probe/Cargo.toml').write_text(PROBE_MANIFEST)
e=R/'sampler-probe-complete-build-inputs';e.mkdir(exist_ok=True)
assert not (e/'receipt.json').exists(), 'Refuse unchanged gate replay'
reservation=0
for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v=p.read_text().strip()
        if v!='max' and (p.parent/'cgroup.procs').read_text().strip():reservation+=int(v)
    except OSError:pass
assert reservation+8*2**30<=55*2**30, reservation
cmd=['/home/dombarker/.cargo/bin/cargo','run','--release','--offline','-j','4','-p','aspis-ser-join-probe']
env=os.environ.copy();env['PATH']='/home/dombarker/.cargo/bin:'+env['PATH'];env['CARGO_TARGET_DIR']=str(R/'target')
print('Expected time: compilation, then two fixed 22-query source-sampler probes; no elimination',flush=True)
with (e/'stdout.log').open('w') as out,(e/'stderr.log').open('w') as err:
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(e/'time.log'),'timeout','300',*cmd],cwd=R/'source',env=env,stdout=out,stderr=err,timeout=360).returncode
r=dict(exit=rc,command=cmd,populated_reservation_bytes=reservation,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,expected_time='compilation then two fixed 22-query sampler probes',stdout=(e/'stdout.log').read_text(),stderr=(e/'stderr.log').read_text(),timing=(e/'time.log').read_text(),rustc=subprocess.check_output(['rustc','-Vv'],env=env,text=True),cargo=subprocess.check_output(['cargo','-V'],env=env,text=True))
(e/'receipt.json').write_text(json.dumps(r,indent=2)+'\\n')
print(json.dumps(r))
'''.replace('REMOTE',repr(REMOTE)).replace('PROBE_MANIFEST',repr(probe_manifest)).replace('MANIFEST',repr(manifest))
output = ssh('python3 -c '+shlex.quote(script))
print(output.splitlines()[0])
r = json.loads(output.splitlines()[-1])
print(json.dumps({k:r[k] for k in ['exit','stdout','timing']}))
files = sorted((ROOT/'crates/aspis-core/src').rglob('*.rs'))
r['source_revision'] = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
r['build_script_sha256'] = hashlib.sha256((ROOT/'crates/aspis-core/build.rs').read_bytes()).hexdigest()
r['source_tree'] = [{'path':str(p.relative_to(ROOT)), 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
r['probe_sha256'] = hashlib.sha256((HERE/'ser-join-sampler-probe.rs').read_bytes()).hexdigest()
r['exact_target'] = 'aspis_core::r0_transcript::queries_from_pairs, two explicit q22 orders'
r['classification'] = 'Native source-level regression witness, not a universal P6 certificate or concrete-hash preimage'
(HERE/'ser-join-sampler-evidence.json').write_text(json.dumps(r,indent=2)+'\n')
assert r['exit'] == 0
