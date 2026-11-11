#!/usr/bin/env python3
"""Stage unchanged field/R0 modules, compile optimized Rust, and record evidence."""
import argparse, hashlib, json, os, pathlib, resource, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--c1-only',action='store_true');p.add_argument('--structured',action='store_true');p.add_argument('--details',action='store_true');p.add_argument('--all',action='store_true');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3];out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
stage=out/'source';stage.mkdir(exist_ok=True)
paths=[root/'crates/aspis-core/src/field.rs',root/'crates/aspis-core/src/field',root/'crates/aspis-core/src/r0']
manifest={}
for src in paths:
    if src.is_dir():shutil.copytree(src,stage/src.name,dirs_exist_ok=True)
    else:shutil.copy2(src,stage/src.name)
    for f in (src.rglob('*') if src.is_dir() else [src]):
        if f.is_file():manifest[str(f.relative_to(root))]=hashlib.sha256(f.read_bytes()).hexdigest()
for f in [here/'probe.rs',here/'run.py']:
    manifest[str(f.relative_to(root))]=hashlib.sha256(f.read_bytes()).hexdigest()
    shutil.copy2(f,out/f.name)
(stage/'lib.rs').write_text('extern crate alloc;\npub mod field;\npub mod r0;\n')
rustc=shutil.which('rustc') or str(pathlib.Path.home()/'.cargo/bin/rustc')
cgroup=None
if pathlib.Path('/proc/self/cgroup').exists():
    cg=pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1];cgroup=pathlib.Path('/sys/fs/cgroup')/cg.lstrip('/')
def cgread(n):
    try:return (cgroup/n).read_text().strip() if cgroup else None
    except FileNotFoundError:return None
caps={n:cgread(n) for n in ['memory.high','memory.max','memory.swap.max']}
if cgroup and (caps['memory.swap.max']!='0' or caps['memory.max'] in [None,'max']):raise SystemExit('Requires explicit memory cap and MemorySwapMax=0')
commands=[['--edition=2021','--crate-name','z4_core','--crate-type','rlib','-C','opt-level=3','-C','overflow-checks=yes',str(stage/'lib.rs'),'-o',str(out/'libz4_core.rlib')],['--edition=2021','-C','opt-level=3','-C','overflow-checks=yes',str(here/'probe.rs'),'--extern',f'z4_core={out}/libz4_core.rlib','-o',str(out/'probe')]]
receipts=[]
def run(command,label):
    t=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        child=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
        _,status,ru=os.wait4(child.pid,0)
        child.returncode=os.waitstatus_to_exitcode(status)
    result=child
    receipt=dict(target=label,command=command,exit_status=result.returncode,wall_seconds=time.monotonic()-t,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=cgread('memory.peak'),cgroup_swap_peak=cgread('memory.swap.peak'))
    receipts.append(receipt);print(json.dumps(receipt),flush=True)
    return result.returncode
exit_status=0
for i,cmd in enumerate(commands):
    exit_status=run([rustc]+cmd,f'compile-{i}')
    if exit_status:break
if not exit_status:exit_status=run([str(out/'probe')]+(['--c1-only'] if args.c1_only else [])+(['--structured'] if args.structured else [])+(['--details'] if args.details else [])+(['--all'] if args.all else []),'probe')
(out/'evidence.json').write_text(json.dumps(dict(base_revision='805f9c102f74f16b5e3d21496e108d963ed27d10',rustc=subprocess.check_output([rustc,'--version'],text=True).strip(),caps=caps,source_sha256=manifest,model_source_sha256=json.loads((here/'SOURCE_MANIFEST.json').read_text()),receipts=receipts,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
raise SystemExit(exit_status)
