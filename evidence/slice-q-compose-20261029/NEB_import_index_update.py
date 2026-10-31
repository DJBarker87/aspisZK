from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent;rev='f9a70eb61e';rev=subprocess.check_output(['git','rev-parse',rev],cwd=R,text=True).strip();prefix='evidence/slice-q-leaves-20261029/'
attempts=[f'NEA_K{n:03}' for n in [40,41,42,43,46,47,48,49,50,51]];names=['NEA_CLOSED.json','NEA_HANDOFF.md','NEA_STOP_AUDIT.json','NEA_Index.lean','NEA_INDEX.md','NEA_TypeResolution.md']
files=[]
for p in subprocess.check_output(['git','ls-tree','-r','--name-only',rev,prefix],cwd=R,text=True).splitlines():
 rel=p.removeprefix(prefix)
 if rel not in names and not any(rel.startswith(a+'/') or rel.startswith(a+'-') or rel==a+'.json' for a in attempts):continue
 raw=subprocess.check_output(['git','show',rev+':'+p],cwd=R);assert len(raw)<=20*1024**2;q=E/'NEB_IMPORTED_INDEX_FINAL'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw);files.append(dict(path=str(q.relative_to(R)),source_path=p,sha256=hashlib.sha256(raw).hexdigest()))
(E/'NEB_INDEX_FINAL_IMPORTS.json').write_text(json.dumps(dict(revision=rev,files=files,reason='Immutable final constructor Result-shape controls; peer branch ref absent; final committed handoff reachable via research history. Never read live peer worktree.'),indent=1)+'\n');print('imported',len(files))
