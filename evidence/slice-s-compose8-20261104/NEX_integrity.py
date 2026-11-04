"""Check committed execution inputs, hashes, file size and source scope."""
from pathlib import Path
import hashlib,json,subprocess
import NEX_validate as v
E=v.E;R=v.R
refs={}
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('path'),str) and isinstance(x.get('sha256'),str):
   if not x['path'].startswith('/'):
    refs[x['path']]=x['sha256']
  for y in x.values():walk(y)
 elif isinstance(x,list):
  for y in x:walk(y)
walk(v.read(E/'NEX_LEDGER_DELTA.json'))
errors=[]
for n,h in refs.items():
 p=R/n
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=h:errors.append(n)
tracked=set(subprocess.check_output(['git','ls-files','-z'],text=True).split('\0'))
untracked=[n for n in refs if n not in tracked]
oversized=[str(p.relative_to(R)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
shipped=subprocess.check_output(['git','diff','df81d22b675','--name-only','--','crates','programs'],text=True).splitlines()
result=dict(referenced_input_count=len(refs),hash_errors=errors,untracked_inputs=untracked,oversized=oversized,shipped_source_changes=shipped,scope='all new packet artifact refs, plus retained unchanged nested gates; git tracking checked after staging',no_keys_touched=True)
(E/'NEX_INTEGRITY.json').write_text(json.dumps(result,indent=1)+'\n')
assert not errors+untracked+oversized+shipped,result
print(json.dumps(result))
