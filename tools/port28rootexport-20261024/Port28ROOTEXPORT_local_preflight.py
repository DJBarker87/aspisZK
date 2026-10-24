#!/usr/bin/env python3
"""New raw diagnostic input checks only. No compiler or source-only rerun."""
import ast,hashlib,json,re,resource,subprocess
from pathlib import Path
T=Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port28rootexport-20261024'
HOME=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0')
def pin(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
def no_comments(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif not quoted and s.startswith('/-',i):depth=1;i+=2
        elif not quoted and s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':quoted=not quoted;out.append(' ');i+=1
        elif quoted and s[i]=='\\':i+=2
        else:out.append(' ' if quoted else s[i]);i+=1
    assert depth==0
    return ''.join(out)
def main():
    for p in T.glob('*.py'):ast.parse(p.read_text())
    lean=(T/'Port28ROOTEXPORT_Raw.lean').read_text()
    assert re.findall(r'^import (.*)$',lean,re.M)==['Lean']
    assert all(x not in lean for x in ['maxHeartbeats','maxRecDepth','importModules','addDeclCore'])
    pre=json.loads((E/'Port28ROOTEXPORT_copy-pre-v3.json').read_text())
    post=json.loads((E/'Port28ROOTEXPORT_copy-post-v3.json').read_text())
    assert pre['allowed_to_enter'] and post['allowed_to_enter']
    current=json.loads((E/'Port28ROOTEXPORT_copy.json').read_text());old=json.loads((E/'Port28ROOTEXPORT_copy-failed-v1.json').read_text())
    assert current['exit_status']==0
    retained=Path(current['retained']);objs=old['objects']+current['objects'];sources={}
    for x in objs:
        p=Path(x['retained_path']);assert not p.is_symlink() and p.stat().st_nlink==1
        assert pin(p)['sha256']==x['sha256']==x['copy_sha256']==x['post_sha256']
        assert x['path'] not in sources;sources[x['path']]=x
    mains=[x for x in objs if x['suffix']=='']
    lines=[]
    for x in mains:
        # Reused and new stages keep each module's part set together.
        for suffix in ('.server','.private'):
            src=x['path']+suffix
            if src in sources:assert sources[src]['retained_path']==x['retained_path']+suffix
        lines.append('\t'.join([str(x['root_index']),x['module'],x['retained_path']]))
    (retained/'objects.tsv').write_text('\n'.join(lines)+'\n')
    plan=json.loads((E/'Port28ROOTEXPORT_seed-plan.json').read_text())
    (retained/'seeds.tsv').write_text(''.join(s['module']+'\t'+s['name']+'\n' for s in plan['seeds']))
    todo=['Lean'];seen={};parts=[]
    while todo:
        m=todo.pop()
        if m in seen:continue
        p=HOME/'src/lean'/(m.replace('.','/')+'.lean');o=HOME/'lib/lean'/(m.replace('.','/')+'.olean')
        assert p.is_file() and o.is_file(),m
        text=no_comments(p.read_text());deps=re.findall(r'^(?:(?:public|meta) )*import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)',text,re.M)
        if m!='Init.Prelude' and not re.search(r'^prelude\s*$',text,re.M):deps+=['Init']
        seen[m]=dict(source=pin(p),imports=deps)
        for suffix in ('','.server','.private'):
            q=Path(str(o)+suffix)
            if q.exists():assert not q.is_symlink();parts.append(pin(q))
        todo.extend(deps)
    # Standard-core leaves can be identified in any installed core object;
    # all parts are pinned, but core modules are never project transports.
    core=list(sorted((HOME/'lib/lean').rglob('*.olean')))
    already={p['path'] for p in parts}
    for o in core:
        for suffix in ('','.server','.private'):
            q=Path(str(o)+suffix)
            if q.exists() and str(q) not in already:
                assert not q.is_symlink();parts.append(pin(q));already.add(str(q))
    (retained/'core.tsv').write_text(''.join(str(p)+'\n' for p in core))
    runtime=[pin(HOME/'bin/lean')]
    for folder in [HOME/'lib',HOME/'lib/lean']:
        for p in sorted(folder.glob('*.dylib')):
            if not p.is_symlink():runtime.append(pin(p))
    full=dict(warm_core_modules=seen,core_parts=parts,runtime=runtime,object_parts=objs,
              tool=pin(T/'Port28ROOTEXPORT_Raw.lean'),inputs=[pin(retained/n) for n in ['objects.tsv','seeds.tsv','core.tsv']])
    raw=json.dumps(full,indent=2).encode();(retained/'diagnostic-inputs.json').write_bytes(raw)
    u=resource.getrusage(0)
    summary=dict(status='PASS new diagnostic static/input preflight',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        retained=str(retained),full_manifest=pin(retained/'diagnostic-inputs.json'),core_import_modules=len(seen),project_main_origins=len(mains),project_parts=len(objs),core_parts=len(parts),
        tool=full['tool'],runtime=runtime,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,
        lean_invocations=0,print_axioms='N/A: input data only; no theorem',missing_seed_modules=sorted({s['module'] for s in plan['seeds']}-{x['module'] for x in mains}))
    (E/'Port28ROOTEXPORT_diagnostic-preflight.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
if __name__=='__main__':main()
