#!/usr/bin/env python3
"""Build/run the optimized Z9 computation (Z8c gate and D23 decomposition on the
R1 payload) and preserve source/evidence. Adapted from run-z8e.py.

One probe process per (structure, vector, gamma) inside this one capped scope;
per-process receipts. Default structures A,B,I,J, vectors 0..4, gammas 0,1.
`--summarize DIR` re-parses an existing output directory only.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--preflight',action='store_true');p.add_argument('--vectors',type=int,default=5);p.add_argument('--jobs',type=int,default=5)
p.add_argument('--structures',default='A,B,I,J');p.add_argument('--gammas',default='0,1');p.add_argument('--revision',default='unknown');p.add_argument('--summarize');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3]
STRUCTS=args.structures.split(',');GAMMAS=[int(g) for g in args.gammas.split(',')]

def kv(text):
    out={}
    for k,x in re.findall(r'(\w+)=(\[[^\]]*\]|\[\[.*?\]\]|[^\s\[]+)',text):
        try:out[k]=json.loads(x)
        except Exception:out[k]=x
    return out

def parse(log_dir):
    ref={}
    for line in (here/'probe-C.log').read_text().splitlines():
        m=re.match(r'(CHALLENGE trial=(\d+) .*)',line)
        if m:ref[int(m.group(2))]=line
    out={'jobs':[]}
    for f in sorted(log_dir.glob('probe-*-*-g*.log')):
        s,v,g=re.match(r'probe-(\w+)-(\d+)-g(\d+)\.log',f.name).groups()
        r={'structure':s,'vector':int(v),'gamma':int(g),'replay_challenge_match':None,'explain':{},'results':{},'lines':{}}
        for line in f.read_text().splitlines():
            tag=line.split(' ')[0]
            if line.startswith('CHALLENGE '):r['replay_challenge_match']=(line==ref.get(int(v)))
            elif tag=='Z9_EXPLAIN':d=kv(line);r['explain'][d['kind']]=d
            elif tag=='RESULT':d=kv(line);r['results'][line.split(' ')[4]]=d
            elif tag.startswith('Z9_') or tag=='STOP':
                if tag in ('Z9_RANKS',):d=kv(line);r['lines'].setdefault(tag,{})[d['kind']]=d
                else:r['lines'][tag]=kv(line)
                if tag in ('Z9_DONE','Z9_PREFLIGHT_DONE'):r['wall_seconds']=float(line.split('wall_seconds=')[1])
        out['jobs'].append(r)
    return out

def table(summary):
    lines=[]
    for r in summary['jobs']:
        L=r['lines'];pu=L.get('Z9_GATE_PURE',{});bc=L.get('Z9_BCOND',{});vd=L.get('Z9_VD',{});vg=L.get('Z9_VG',{});ga=L.get('Z9_GATE',{});pc=L.get('Z9_PCS_BLOCK',{})
        ex=' '.join(f"{k}:ann={d.get('annihilator_dim')},unexpl={d.get('unexplained_dim')}" for k,d in r['explain'].items())
        lines.append(f"{r['structure']} v{r['vector']} g{r['gamma']} replay={r['replay_challenge_match']} silent={pu.get('silent_rank')} retained={pu.get('initial_retained_rank')} B0={bc.get('bat_rank_on_ker_own')} BkerR={bc.get('bat_rank_on_ker_own_and_ker_R')} bcond={bc.get('bcond_holds')} VD={vd.get('bat_rank')} VG={vg.get('bat_rank')} asm={vg.get('assembly_rank')} eq={vg.get('b0_equals_vd_plus_vg')} pcs={pc.get('rank_bat_plus_d_own')}/{pc.get('of')} i'={ga.get('i_pass')} ii'={ga.get('ii_pass')} {ex} wall={r.get('wall_seconds')}")
    return '\n'.join(lines)

if args.summarize:
    d=pathlib.Path(args.summarize).resolve();s=parse(d)
    (d/'summary.json').write_text(json.dumps(s,indent=1)+'\n');print(table(s));raise SystemExit(0)

out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(name):
    try:return (cg/name).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires explicit MemoryHigh=3G, MemoryMax=4G and MemorySwapMax=0')
manifest={}
files=[root/'Cargo.toml',here/'Cargo.toml',here/'Cargo.lock',here/'probe.rs',here/'probe-C.log',here/'run-z9.py']+sorted(here.glob('z*.rs'))
for crate in ['aspis-core','aspis-statement','aspis-prover']:
    files.extend(sorted((root/'crates'/crate/'src').rglob('*.rs')));files.append(root/'crates'/crate/'Cargo.toml')
    if (root/'crates'/crate/'build.rs').exists():files.append(root/'crates'/crate/'build.rs')
for f in files:
    if not f.exists():raise SystemExit(f'Missing source: {f}')
    manifest[str(f.relative_to(root))]=hashlib.sha256(f.read_bytes()).hexdigest()
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root)
        _,status,ru=os.wait4(proc.pid,0);rc=os.waitstatus_to_exitcode(status)
    receipt=dict(target=label,command=cmd,source_revision=args.revision,exit_status=rc,wall_seconds=time.monotonic()-start,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(receipt);print(json.dumps(receipt),flush=True);return rc
def evidence(status,stop=None):
    (out/'evidence.json').write_text(json.dumps(dict(source_revision=args.revision,rustc=subprocess.check_output([str(pathlib.Path(cargo).with_name('rustc')),'--version'],text=True).strip(),caps=caps,scope=str(cg),mode='z9',preflight=args.preflight,structures=STRUCTS,gammas=GAMMAS,vectors=args.vectors,concurrency=args.jobs,source_sha256=manifest,receipts=receipts,stop=stop,exit_status=status,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
binary=str(here/'target/release/probe')
def job(s,v,g,extra=()):return run([binary,'--z9','--structure',s,'--vector',str(v),'--gamma',str(g),*extra],f'probe-{s}-{v}-g{g}')
start=time.monotonic()
status=run([cargo,'build','--release','--locked','--offline','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
if status!=0:evidence(status,'compile');raise SystemExit(status)
if args.preflight:
    status=job('A',0,GAMMAS[0],['--preflight']);evidence(status);print(table(parse(out)));raise SystemExit(status)
jobs_list=[(s,v,g) for g in GAMMAS for s in STRUCTS for v in range(args.vectors)]
with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
    codes=list(ex.map(lambda x:job(*x),jobs_list))
status=0 if all(c==0 for c in codes) else 1
summary=parse(out);summary['total_wall_seconds']=time.monotonic()-start
(out/'summary.json').write_text(json.dumps(summary,indent=1)+'\n');print(table(summary))
evidence(status);raise SystemExit(status)
