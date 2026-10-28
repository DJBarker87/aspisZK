"""Nominal-only constructor-function names; no LLBC types, bodies or calls change."""
from pathlib import Path
import json,hashlib,copy,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin30-20261028'
p=E/'pv30-outer-charon-02.llbc';x=json.loads(p.read_text());y=copy.deepcopy(x);changes=[]
for r in y['translated']['fun_decls']:
 if not r:continue
 m=r['item_meta'];name=m['name']
 if len(name)>=2 and 'Ident' in name[-1] and 'Ident' in name[-2] and name[-2]['Ident'][0]=='PoolV1PairTraceErrorV1':
  old=m['attr_info']['rename'];new=name[-1]['Ident'][0]+'Ctor';m['attr_info']['rename']=new
  changes.append(dict(id=r['def_id'],old=old,new=new))
z=copy.deepcopy(y)
for c in changes:next(r for r in z['translated']['fun_decls'] if r and r['def_id']==c['id'])['item_meta']['attr_info']['rename']=c['old']
assert z==x and changes
q=E/'pv30-outer-names-02.llbc';q.write_text(json.dumps(y))
(E/'constructor-renames.json').write_text(json.dumps(dict(original_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),renamed_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),changes=changes,all_other_json_identical=z==x),indent=2)+'\n')
subprocess.run(['scp','-q',str(q),'dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-runjoin-20261026/evidence/'+q.name],check=True)
