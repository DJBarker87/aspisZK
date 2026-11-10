#!/usr/bin/env python3
"""NPK_ collector: dep-info (.d) and the -v rustc command lines of one kept target dir -> JSON.
Usage: NPK_collect.py <target_dir> <src_root> <stderr.log> <out.json>
Read-only on the target and source; writes only <out.json>."""
import sys,json,hashlib,re,shlex,pathlib,os
tgt,src,log,out=[pathlib.Path(a).resolve() for a in sys.argv[1:5]]
HOME='/home/dombarker'
def sha(p):
    try: return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
    except Exception as e: return 'ERR:'+type(e).__name__
def parse_d(p):
    txt=p.read_text()
    deps=[];envs=[]
    for line in txt.splitlines():
        if line.startswith('# env-dep:'): envs.append(line[len('# env-dep:'):]); continue
        if not line.strip() or line.startswith('#'): continue
        # "target: dep dep ..." with backslash-escaped spaces
        head,_,rest=line.partition(': ')
        if not _ and line.endswith(':'): continue
        if pathlib.Path(head).suffix!='.d': continue
        toks=re.split(r'(?<!\\) ',rest.strip())
        deps+= [t.replace('\\ ',' ') for t in toks if t]
    return deps,envs
def classify(f):
    if not f.startswith('/'): return 'repo',f
    s=str(src)+'/'
    if f.startswith(s): return 'repo',f[len(s):]
    if f.startswith(str(tgt)+'/'): return 'generated',f[len(str(tgt))+1:]
    if f.startswith(HOME+'/.cargo/registry/'): return 'registry',f[len(HOME+'/.cargo/registry/'):]
    if '/platform-tools/' in f or '/.rustup/' in f: return 'toolchain',f
    return 'other',f
units=[]
for d in sorted(list(tgt.glob('sbpf-solana-solana/release/deps/*.d'))+list(tgt.glob('release/deps/*.d'))+list(tgt.glob('release/build/*/*.d'))+list(tgt.glob('sbpf-solana-solana/release/build/*/*.d'))):
    deps,envs=parse_d(d)
    rows=[]
    for f in deps:
        k,r=classify(f)
        absf=f if f.startswith('/') else str(src/f)
        rows.append(dict(kind=k,path=r,sha256=sha(absf) if k in('repo','generated') else None))
    units.append(dict(depinfo=str(d.relative_to(tgt)),files=rows,env_deps=envs))
# rustc command lines from cargo -v
cmds=[]
for line in log.read_text(errors='replace').splitlines():
    m=re.match(r'\s*Running `(.*)`\s*$',line)
    if not m or 'rustc' not in m.group(1).split(' ')[0] and ' rustc ' not in m.group(1): continue
    c=m.group(1)
    try: argv=shlex.split(c)
    except ValueError: continue
    if '--crate-name' not in argv: continue
    name=argv[argv.index('--crate-name')+1]
    feats=sorted(re.findall(r'feature="([^"]+)"',' '.join(argv[i+1] for i,a in enumerate(argv) if a=='--cfg')))
    tg=argv[argv.index('--target')+1] if '--target' in argv else 'host'
    srcf=[a for a in argv if a.endswith('.rs') and not a.startswith('-')]
    ct=[argv[i+1] for i,a in enumerate(argv) if a=='--crate-type']
    md=[a for a in argv if a.startswith('metadata=')]
    cmds.append(dict(crate=name,target=tg,crate_types=ct,root=srcf[:1],features=feats,metadata=md[:1],
                     codegen=[argv[i+1] for i,a in enumerate(argv) if a=='-C']))
out.write_text(json.dumps(dict(target_dir=str(tgt),src_root=str(src),units=units,rustc=cmds),indent=1)+'\n')
print(len(units),'units',len(cmds),'rustc invocations')
