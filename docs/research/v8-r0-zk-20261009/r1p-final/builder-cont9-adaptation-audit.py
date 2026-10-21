#!/usr/bin/env python3
"""Inspect metadata-only LLBC changes and enumerate all unproved externals."""
import subprocess,pathlib,json
H=pathlib.Path(__file__).resolve().parent
script='''import json,pathlib,hashlib,re
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref9-20261021')
E=R/'drop-opaque-validator';a=json.loads((E/'admission.llbc').read_text());b=json.loads((E/'admission-renamed.llbc').read_text());diff=[]
def go(a,b,p):
 if a==b:return
 if type(a)!=type(b):diff.append(dict(path=p,before=a,after=b));return
 if isinstance(a,dict):
  assert a.keys()==b.keys()
  for k in a:go(a[k],b[k],p+'/'+k)
 elif isinstance(a,list):
  assert len(a)==len(b)
  for i,(u,v) in enumerate(zip(a,b)):go(u,v,p+'/'+str(i))
 else:diff.append(dict(path=p,before=a,after=b))
go(a,b,'')
assert diff and all('/item_meta/name/' in x['path'] or x['path'].startswith('/translated/item_names/') or x['path'].endswith('/item_meta/attr_info/rename') for x in diff),diff
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
gen=E/'generated/Admission-renamed.lean';s=gen.read_text()
print(json.dumps(dict(metadata_only=True,changes=diff,source_revision='5aef25c53',artifacts={str(p.relative_to(R)):pin(p) for p in [E/'admission.llbc',E/'admission-renamed.llbc',gen]},unproved_externals=re.findall(r'^axiom ([^\\s(]+)',s,re.M),drop_opaque=[x for x in b['translated']['fun_decls'] if x and x['item_meta']['name'][-1]=={'Ident':['drop',0]} and 'state_only_trace' in str(x['item_meta']['name'])],validator_substitution=json.loads((R/'validator-substitution.json').read_text()))))
'''
r=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True)
d=json.loads(r)
(H/'builder-cont9-adaptation-audit.json').write_text(json.dumps(d,indent=2)+'\n')
print('metadata-only changes',len(d['changes']),'unproved externals',len(d['unproved_externals']))
