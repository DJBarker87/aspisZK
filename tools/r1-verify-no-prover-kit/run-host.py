#!/usr/bin/env python3
"""One capped focused native or extraction job, with immutable input receipts."""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--input-manifest',type=Path);ap.add_argument('--label',required=True);ap.add_argument('--cwd',type=Path,required=True)
    ap.add_argument('--kind',choices=['native','extraction'],required=True)
    ap.add_argument('--timeout',type=int,default=180);ap.add_argument('command',nargs=argparse.REMAINDER)
    a=ap.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command;assert cmd
    cgtext=Path('/proc/self/cgroup').read_text().strip();assert cgtext.startswith('0::')
    cg=Path('/sys/fs/cgroup')/cgtext[3:].lstrip('/')
    limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
    assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
    manifest=a.input_manifest or a.root/'inputs.json'
    inputs=json.loads(manifest.read_text())
    for name,h in inputs['files'].items():assert sha(a.root/name)==h,name
    run=a.root/'runs'/a.label;run.mkdir(parents=True,exist_ok=False)
    (run/'input-manifest.json').write_bytes(manifest.read_bytes())
    (run/'runner.py').write_bytes(Path(__file__).read_bytes())
    env=dict(os.environ);env['CARGO_BUILD_JOBS']='1';env['CARGO_NET_OFFLINE']='true'
    toolchain='stable' if a.kind=='native' else 'nightly-2026-06-01'
    env['RUSTUP_TOOLCHAIN']=toolchain
    env['CARGO_TARGET_DIR']=str(a.root/('cargo-target' if a.kind=='native' else 'extract-target'))
    env['PATH']='/home/dombarker/.cargo/bin:'+env.get('PATH','')
    if a.kind=='extraction':
        lib=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib')
        env['LD_LIBRARY_PATH']=str(lib)+':'+env.get('LD_LIBRARY_PATH','')
        env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']='true'
        env['CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL']='3'
    pinned={k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR']}
    for k in ['LD_LIBRARY_PATH','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL']:
        if k in env:pinned[k]=env[k]
    (run/'environment.json').write_text(json.dumps(pinned,indent=2)+'\n')
    versions=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-vV'],env=env,text=True)
    before=Path('/proc/meminfo').read_text();start=time.monotonic()
    with (run/'stdout.log').open('x') as out, (run/'stderr.log').open('x') as err:
        p=subprocess.run(['/usr/bin/time','-v','-o',str(run/'time.log'),'timeout','--signal=KILL',str(a.timeout),*cmd],cwd=a.cwd,env=env,stdout=out,stderr=err)
    wall=time.monotonic()-start;timing=(run/'time.log').read_text()
    def metric(name):
        m=re.search(re.escape(name)+r':\s*(\d+)',timing);return int(m[1]) if m else None
    receipt={'label':a.label,'kind':a.kind,'command':cmd,'cwd':str(a.cwd),'source_revision':inputs['source_revision'],'input_manifest_sha256':sha(manifest),'exit_status':p.returncode,'wall_seconds':wall,'peak_rss_kib':metric('Maximum resident set size (kbytes)'),'process_swaps':metric('Swaps'),'cgroup':cgtext,'limits':limits,'cgroup_memory_peak_bytes':int((cg/'memory.peak').read_text()),'cgroup_swap_current':(cg/'memory.swap.current').read_text().strip(),'memory_events':(cg/'memory.events').read_text(),'runner_sha256':sha(Path(__file__)),'rustc_version':versions,'timeout_seconds':a.timeout,'system_swap_before':[x for x in before.splitlines() if x.startswith('Swap')],'system_swap_after':[x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('Swap')],'axioms':'N/A: Rust/tool stage, not a Lean theorem check'}
    receipt['stdout_sha256']=sha(run/'stdout.log');receipt['stderr_sha256']=sha(run/'stderr.log')
    import shlex
    artifacts={}
    for match in re.finditer(r"Running `([^`]+)`",(run/'stderr.log').read_text()):
        command_parts=shlex.split(match[1])
        for part in command_parts:
            candidate=Path(part)
            if part.startswith(str(a.root/'cargo-target/release')+'/') and candidate.suffix not in ['.rlib','.rmeta'] and candidate.is_file():
                artifacts[part]={'sha256':sha(candidate),'bytes':candidate.stat().st_size}
                break
    receipt['artifacts']=artifacts
    (run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
    raise SystemExit(p.returncode)
if __name__=='__main__':main()
