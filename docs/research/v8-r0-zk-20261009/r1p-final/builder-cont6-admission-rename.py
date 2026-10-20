#!/usr/bin/env python3
"""Host-only metadata rename of an Aeneas constructor/function name clash."""
import json,pathlib,hashlib,subprocess,os
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref6-20261021')
E=R/'admission-common';raw=E/'admission.llbc';d=json.loads(raw.read_text())
assert d['has_errors'] is False
old=d['translated']['fun_decls'][9]['item_meta']['name']
assert old[-2:]==[{'Ident':['PoolV1PairTraceErrorV1',0]},{'Ident':['PairLeaf',0]}]
new=old[:-1]+[{'Ident':['PairLeafCtor',0]}]
changes=[]
def visit(x,path):
    if isinstance(x,dict):
        for k,v in x.items():
            if v==old: x[k]=new;changes.append(path+'/'+k)
            elif isinstance(v,(list,dict)):visit(v,path+'/'+k)
    elif isinstance(x,list):
        for i,v in enumerate(x):
            if v==old:x[i]=new;changes.append(path+'/'+str(i))
            elif isinstance(v,(list,dict)):visit(v,path+'/'+str(i))
visit(d,'')
assert '/translated/fun_decls/9/item_meta/name' in changes
p=E/'admission-renamed.llbc';p.write_text(json.dumps(d))
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
(E/'metadata-rename.json').write_text(json.dumps(dict(old=old,new=new,paths=changes,raw=pin(raw),adapted=pin(p),scope='Identifier metadata only; no bodies, types, control flow, or Rust source modified'),indent=2)+'\n')
reserved=0
for q in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v=q.read_text().strip()
        if v!='max' and (q.parent/'cgroup.procs').read_text().strip():reserved+=int(v)
    except OSError:pass
assert reserved+8*2**30<=55*2**30
out=E/'generated-renamed';out.mkdir(exist_ok=False)
env=os.environ.copy();env.update(ASPIS_SOURCE_REV='0b0e77f5f',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderAdmissionSource','-dest',str(out),'-loops-to-rec','-print-unknown-externals',str(p)]
rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/'aeneas-renamed'),'Translation after identifier metadata rename; no recompilation or arithmetic gate','--','timeout','180',*cmd],cwd=R/'source',env=env).returncode
print('aeneas renamed exit',rc,flush=True)
