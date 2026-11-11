#!/usr/bin/env python3
"""Build/run only the optimized Z6 row-terminal computation and preserve source/evidence."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--preflight',action='store_true');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3];out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(name):
    try:return (cg/name).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires explicit MemoryHigh, MemoryMax and MemorySwapMax=0')
manifest={}
files=[root/'Cargo.toml',here/'Cargo.toml',here/'Cargo.lock',here/'probe.rs',here/'z5.rs',here/'z6.rs',here/'run-z6.py']
for crate in ['aspis-core','aspis-statement','aspis-prover']:
    files.extend((root/'crates'/crate/'src').rglob('*.rs'));files.append(root/'crates'/crate/'Cargo.toml')
    if (root/'crates'/crate/'build.rs').exists():files.append(root/'crates'/crate/'build.rs')
for f in files:
    if not f.exists():raise SystemExit(f'Missing source: {f}')
    rel=f.relative_to(root);manifest[str(rel)]=hashlib.sha256(f.read_bytes()).hexdigest();dest=out/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dest)
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root)
        _,status,ru=os.wait4(proc.pid,0);proc.returncode=os.waitstatus_to_exitcode(status)
    receipt=dict(target=label,command=cmd,exit_status=proc.returncode,wall_seconds=time.monotonic()-start,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(receipt);print(json.dumps(receipt),flush=True);return proc.returncode
status=run([cargo,'build','--release','--locked','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
if status==0:
    status=run([str(here/'target/release/probe'),'--z6']+(['--preflight'] if args.preflight else []),'probe')
(out/'evidence.json').write_text(json.dumps(dict(base_revision='0a9ffe45a1505716ec50fdcd04f17a08de3e2d38',rustc=subprocess.check_output([str(pathlib.Path(cargo).with_name('rustc')),'--version'],text=True).strip(),caps=caps,source_sha256=manifest,receipts=receipts,scope=str(cg),mode='z6',preflight=args.preflight,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
raise SystemExit(status)
