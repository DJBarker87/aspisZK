#!/usr/bin/env python3
"""PCXV_ L187 object tripwire. baseline | check [--full]. Read-only on L187. Sample = 300 random L187 oleans (seed 20261111) + every L187 olean of a rebuild-set module.
check: sample300 hashed every time; rebuild-set part compared by (size,mtime_ns) unless --full (then sha256)."""
import hashlib,json,os,pathlib,random,sys,time
L=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/objs');WS=pathlib.Path('/home/dombarker/project-offloads/codex-pc-pin2-replay-20261111')
mode=sys.argv[1];full='--full' in sys.argv;B=WS/'PCXV_TRIPWIRE_BASELINE.json'
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()
def st(p):s=os.stat(p);return [s.st_size,s.st_mtime_ns]
if mode=='baseline':
    allo=sorted(str(p.relative_to(L)) for p in L.rglob('*.olean'))
    rs={r['module'] for r in json.load(open(WS/'PCXR_REBUILD_SET.json'))['modules']}
    rb=[m.replace('.','/')+'.olean' for m in rs];rb=sorted(x for x in rb if (L/x).is_file())
    random.seed(20261111);samp=sorted(random.sample(allo,300))
    d=dict(utc=time.time(),n_all=len(allo),sample300={x:sha(L/x) for x in samp},rebuild_set={x:dict(sha=sha(L/x),st=st(L/x)) for x in rb})
    B.write_text(json.dumps(d));print('baseline',len(allo),len(samp),len(rb))
else:
    d=json.loads(B.read_text());bad=[]
    for x,h in d['sample300'].items():
        if sha(L/x)!=h:bad.append(x)
    for x,v in d['rebuild_set'].items():
        p=L/x
        if not p.is_file() or st(p)!=v['st'] or (full and sha(p)!=v['sha']):bad.append(x)
    n=sum(1 for _ in L.rglob('*.olean'))
    print(json.dumps(dict(utc=time.time(),full=full,changed=bad[:20],n_changed=len(bad),n_all=n,n_all_baseline=d['n_all'],ok=(not bad and n==d['n_all']))))
