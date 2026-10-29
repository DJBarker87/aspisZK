"""Collect only this job's receipts/text evidence; retain raw diagnostic LLBC on host."""
from pathlib import Path
import hashlib,json,lzma,shutil
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1');E=H/'export';E.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in H.glob('N*'):
 if d.is_dir():
  out=E/d.name;out.mkdir(exist_ok=True)
  for p in d.iterdir():
   if p.is_file():shutil.copy2(p,out/p.name)
records=[]
for n in [73340,73341,73343,73346]:
 p=H/f'PV_CX_Entry-N{n}.llbc'
 if not p.exists():continue
 x=json.loads(p.read_text());records.append(dict(attempt=n,path=str(p),bytes=p.stat().st_size,sha256=sha(p),has_errors=x['has_errors'],options=x['translated']['options'],option_count=sum(bool(t and t['item_meta'].get('lang_item')=='Option') for t in x['translated']['type_decls'])))
 if n in [73343,73346]:
  dest=E/(p.name+'.xz')
  if not dest.exists():
   with p.open('rb') as f,lzma.open(dest,'wb',preset=6) as g:shutil.copyfileobj(f,g)
(E/'alternative-llbc-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
for name in ['Main.ml','PrePasses.ml']:
 p=H/'aeneas/src'/name
 (E/(name+'.sha256')).write_text(sha(p)+'\n')
 text=p.read_text().splitlines();ranges=[(575,580)] if name=='Main.ml' else [(811,855),(3280,3295)]
 (E/(name+'.excerpts.txt')).write_text('\n\n'.join('\n'.join(str(i)+': '+text[i-1] for i in range(a,b+1)) for a,b in ranges)+'\n')
p=H.parents[1]/'aeneas-static-build-ocaml52.log';shutil.copy2(p,E/p.name)
print(json.dumps(records))
