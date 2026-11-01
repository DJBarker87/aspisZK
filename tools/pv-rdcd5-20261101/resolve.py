"""Resolve requested proof closure against tracked HEAD and higher priorities.
No compiler, source upload, extraction, native test, or object reuse occurs.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
seen={};order=[]
def go(m):
    if m in seen:return
    candidates=['docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean',
      'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean']
    for p in candidates:
        q=subprocess.run(['git','show','HEAD:'+p],cwd=R,capture_output=True)
        if q.returncode==0:break
    else:raise RuntimeError('Unresolved project module '+m)
    b=q.stdout;deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
    seen[m]=dict(path=p,blob=git('rev-parse','HEAD:'+p).decode().strip(),
      sha256=hashlib.sha256(b).hexdigest(),imports=deps,
      authority='h5 tracked HEAD; not accepted until higher-priority census below passes')
    for dep in deps:
        if dep.startswith('XR'):raise RuntimeError('Forbidden XR import '+dep)
        if dep.startswith('R1Z.'):go(dep)
    order.append(m)
roots=['R1Z.PV_RDCD5_ParserWindows','R1Z.PV_RDCD5_V197',
       'R1Z.PV_RDCD5_V233','R1Z.PV_RDCD5_BufferSource',
       'R1Z.ProverRwSuccessParserSource','R1Z.PV_DL_UpdateSelected']
for m in roots:go(m)
checks={};conflicts=[]
for ref in ['evidence/envj-rebuild-20261026/EJR_final-inventory.json',
 'docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json']:
    raw=git('show','research:'+ref);j=json.loads(raw);hits=[]
    def visit(x):
        if isinstance(x,dict):
            for k in ['module','name']:
                if isinstance(x.get(k),str) and x[k].replace('/','.') in seen:hits.append(x)
            for v in x.values():visit(v)
        elif isinstance(x,list):
            for v in x:visit(v)
    visit(j)
    checks[ref]=dict(blob=git('rev-parse','research:'+ref).decode().strip(),
      sha256=hashlib.sha256(raw).hexdigest(),hits=hits)
    if hits:conflicts.append(dict(authority=ref,entries=hits))
out=dict(revision=git('rev-parse','HEAD').decode().strip(),roots=roots,modules=seen,
 compile_order=order,higher_priority_census=checks,
 status='requires EJR/freeze resolution of hits' if conflicts else 'h5 source resolution ready; no objects accepted',
 conflicts=conflicts,object_reuse='h6 provenance/import/toolchain/prefix check required before any reuse',
 external_authority='h4 pv-replay-20261027 external-object-manifest; verification required before compile',
 duplicate_audit='No new generated Rust declarations; no equivalence or declaration-unification credit. Any encountered extraction pair must be keyed by crate/source/features under dup-1-prime.')
(E/'source-resolution.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'compile-order.txt').write_text('\n'.join(order)+'\n')
print(len(order),'project modules;',len(conflicts),'higher-priority authorities with hits')
