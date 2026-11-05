"""Deterministic import-only canonical retarget; declaration owners are preserved."""
from pathlib import Path
import json,re,hashlib,sys,difflib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry5-20261107';M=E.parent/'owner-dedupe-20261107'
sha=lambda b:hashlib.sha256(b).hexdigest()
paths={p.stem:p for p in P.glob('*.lean') if p.stem not in ['NIJ_ProofDriver','NIJ_ScanDriver'] and not p.stem.startswith('NIJ_Inspect')}
mp={m:m.replace('NIJ_','NIS_',1) for m in paths}
mp.update(json.loads((M/'NIM_PROVENANCE.json').read_text())['module_map'])
rows=[];order=[]
def visit(m):
    if m in order:return
    for dep in re.findall(r'^import ([\w.]+)',paths[m].read_text(),re.M):
        if dep in paths:visit(dep)
    order.append(m)
for m in paths:visit(m)
for m in order:
    raw=paths[m].read_text()
    out=re.sub(r'^import ([\w.]+)',lambda x:'import '+mp.get(x[1],x[1]),raw,flags=re.M)
    if m=='NIJ_COMBINED_IMPORT':out='import NIM_COMBINED_IMPORT\nimport NIM_NHJ_COMBINED_IMPORT\n'+out
    if m=='NIJ_COMBINED_IMPORT' and (E/'NIS_FINAL_IMPORTS.json').exists():
        ls=out.splitlines(True);i=next(i for i,l in enumerate(ls) if not l.startswith('import '));out=''.join(ls[:i])+''.join('import '+x+'\n' for x in json.loads((E/'NIS_FINAL_IMPORTS.json').read_text()))+''.join(ls[i:])
    q=E/(mp[m]+'.lean')
    if '--check' in sys.argv:assert q.read_text()==out
    else:q.write_text(out)
    rows.append(dict(original=str(paths[m].relative_to(E.parents[1])),original_sha256=sha(raw.encode()),module=mp[m],sha256=sha(out.encode()),changes='imports only; original theorem/definition names and proof bodies retained'))
if '--check' not in sys.argv:
    (E/'NIS_RETARGET.json').write_text(json.dumps(dict(module_map=mp,order=[mp[m] for m in order],modules=rows),indent=1)+'\n')
    for old,new in [('NIM_ProofDriver','NIS_ProofDriver'),('NIM_Driver','NIS_ScanDriver')]:
        raw=(M/(old+'.lean')).read_text()
        out=raw.replace('NIM_COMBINED_IMPORT','NIS_COMBINED_IMPORT').replace('NIM_AUDIT_ROOTS.json','NIS_AUDIT_ROOTS.json').replace('NIM_EXPECTED_IMPORTS','NIS_EXPECTED_IMPORTS').replace('NIM_LOADED','NIS_LOADED')
        (E/(new+'.lean')).write_text(out)
        (E/(new+'.diff')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),out.splitlines(True),fromfile=old+'.lean',tofile=new+'.lean')))
print(json.dumps(dict(status='PASS_IMPORT_ONLY_RETARGET',modules=len(rows),order=[mp[m] for m in order])))
