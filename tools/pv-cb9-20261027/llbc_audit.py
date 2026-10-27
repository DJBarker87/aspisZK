"""Read-only proof that attempted LLBC roots contain the shipped bodies."""
from pathlib import Path
import subprocess,shlex,json
p=Path(__file__).resolve().parents[2]/'evidence/pv-cb9-20261027'
code='''import pathlib,json,hashlib
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-cb3-20261026');rows=[]
for q in sorted(p.glob('PV_CB3_CB9Op*.llbc')):
 raw=q.read_bytes();j=json.loads(raw);d=j['translated']
 fs=[f for f in d['fun_decls'] if f];f=fs[0] if fs else None
 def name(f):return '::'.join(e['Ident'][0] if 'Ident' in e else '{impl}' for e in f['item_meta']['name'])
 rows.append(dict(path=str(q),sha256=hashlib.sha256(raw).hexdigest(),has_errors=j['has_errors'],options=d['options'],root=dict(name=name(f),span=f['item_meta']['span'],body_kind=list(f['body']) if isinstance(f.get('body'),dict) else f.get('body'),signature=f['signature']) if f else None,function_count=len(fs),transparent_bodies=sum(isinstance(f.get('body'),dict) for f in fs),option_language_items=[t['item_meta']['name'] for t in d['type_decls'] if t and t['item_meta'].get('lang_item')=='option']))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True,check=True)
(p/'LLBC-AUDIT.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
for x in json.loads(r.stdout):print(x['root']['name'],x['root']['body_kind'],x['function_count'],'functions; has_errors=',x['has_errors'])
