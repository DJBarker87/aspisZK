#!/usr/bin/env python3
"""Build/run only the optimized Z8e computation (T2b-2b-D′: wrap set, low
shadow, conjugate relations, left kernels of V_D and V_G, the G premise and
its query-free split) and preserve source/evidence.

Adapted from run-z8d.py. Each (structure, vector) job is its own probe process
inside this one capped scope; receipts are recorded per process. Default
structure A, vectors 0..4. `--summarize DIR` re-parses an existing output directory only.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time
p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--preflight',action='store_true');p.add_argument('--vectors',type=int,default=5);p.add_argument('--jobs',type=int,default=5);p.add_argument('--structures',default='A');p.add_argument('--summarize');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3]
STRUCTS=args.structures.split(',')

def kv(text):
    out={}
    for k,x in re.findall(r'(\w+)=(\[[^\]]*\]|\[\[.*?\]\]|[^\s\[]+)',text):
        try:out[k]=json.loads(x)
        except Exception:out[k]=x
    return out

def parse(log_dir, vectors):
    ref={}
    for line in (here/'probe-C.log').read_text().splitlines():
        m=re.match(r'(CHALLENGE trial=(\d+) .*)',line)
        if m:ref[('c',int(m.group(2)))]=line
    out={'structures':{}}
    for s in STRUCTS:
        recs=[]
        for v in range(vectors):
            f=log_dir/f'probe-{s}-{v}.log'
            if not f.exists():continue
            r={'vector':v,'replay_challenge_match':None,'explain':{},'lines':{}}
            for line in f.read_text().splitlines():
                tag=line.split(' ')[0]
                body=line.split('vector=',1)[1].split(' ',1)[1] if 'vector=' in line and ' ' in line.split('vector=',1)[1] else line
                if line.startswith('CHALLENGE '):r['replay_challenge_match']=(line==ref.get(('c',v)))
                elif tag=='Z8E_EXPLAIN':d=kv(body);r['explain'][d['kind']]=d
                elif tag.startswith('Z8E_') or tag=='STOP':
                    r['lines'][tag]=kv(body) if tag not in ('Z8E_B',) else body
                    if tag in ('Z8E_DONE','Z8E_PREFLIGHT_DONE'):r['wall_seconds']=float(line.split('wall_seconds=')[1])
            recs.append(r)
        if recs:out['structures'][s]=recs
    return out

def table(summary):
    lines=[]
    for s,recs in summary['structures'].items():
        for r in recs:
            L=r['lines'];pu=L.get('Z8E_GATE_PURE',{});wr=L.get('Z8E_WRAP',{});vg=L.get('Z8E_VG',{});sp=L.get('Z8E_SPLIT',{})
            ex=' '.join(f"{k}:ann={d.get('annihilator_dim')},unexpl={d.get('unexplained_dim')}" for k,d in r['explain'].items())
            lines.append(f"{s} v{r['vector']} silent={pu.get('silent_rank')} wz={wr.get('wz_dim_k4')} shadow={wr.get('low_shadow_rank')} vd={L.get('Z8E_VD',{}).get('bat_rank')} vg={vg.get('bat_rank')} asm={vg.get('assembly_rank')} t={vg.get('t_rank_on_V_G')} g3={L.get('Z8E_G3',{}).get('t_rank')} ta={sp.get('t_rank_query_free')} eT={sp.get('e_rank_on_ker_t')} g2={L.get('Z8E_G2',{}).get('rank')} star={L.get('Z8E_STAR',{}).get('mismatches')} {ex} wall={r.get('wall_seconds')}")
    return '\n'.join(lines)

if args.summarize:
    d=pathlib.Path(args.summarize).resolve();s=parse(d,args.vectors)
    (d/'summary.json').write_text(json.dumps(s,indent=1)+'\n');print(table(s));raise SystemExit(0)

out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(name):
    try:return (cg/name).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires explicit MemoryHigh, MemoryMax and MemorySwapMax=0')
manifest={}
files=[root/'Cargo.toml',here/'Cargo.toml',here/'Cargo.lock',here/'probe.rs',here/'z5.rs',here/'z6.rs',here/'z7.rs',here/'z8.rs',here/'z8b.rs',here/'z8c.rs',here/'z8d.rs',here/'z8e.rs',here/'run-z8e.py',here/'probe-C.log']
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
def evidence(status,stop=None):
    (out/'evidence.json').write_text(json.dumps(dict(base_revision='ccefdebd1',rustc=subprocess.check_output([str(pathlib.Path(cargo).with_name('rustc')),'--version'],text=True).strip(),caps=caps,source_sha256=manifest,receipts=receipts,scope=str(cg),mode='z8e',preflight=args.preflight,structures=STRUCTS,vectors=args.vectors,concurrency=args.jobs,stop=stop,exit_status=status,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
binary=str(here/'target/release/probe')
def job(s,v,extra=()):return run([binary,'--z8e','--structure',s,'--vector',str(v),*extra],f'probe-{s}-{v}')
start=time.monotonic()
status=run([cargo,'build','--release','--locked','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
if status!=0:evidence(status,'compile');raise SystemExit(status)
if args.preflight:
    status=job('A',0,['--preflight']);evidence(status);raise SystemExit(status)
jobs_list=[(s,v) for s in STRUCTS for v in range(args.vectors)]
with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
    codes=list(ex.map(lambda sv:job(*sv),jobs_list))
status=0 if all(c==0 for c in codes) else 1
with (out/'probe-Z8e.log').open('w') as log:
    for s in STRUCTS:
        for v in range(args.vectors):
            f=out/f'probe-{s}-{v}.log'
            if f.exists():log.write(f.read_text())
summary=parse(out,args.vectors);summary['total_probe_wall_seconds']=time.monotonic()-start
(out/'summary.json').write_text(json.dumps(summary,indent=1)+'\n');print(table(summary))
evidence(status);raise SystemExit(status)
