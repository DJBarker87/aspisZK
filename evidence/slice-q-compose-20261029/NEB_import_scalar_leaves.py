from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent;rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();prefix='evidence/native-front5-20261028/'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,prefix],cwd=R,text=True).splitlines();attempts=[f'NDH_K{n:03}' for n in [1,2,3,4,11,12]];selected=[]
for p in paths:
 rel=p.removeprefix(prefix)
 if any(rel.startswith(a+'/') or rel.startswith(a+'-') or rel==a+'.json' for a in attempts) or rel in ['NDH_E001/receipt.json','NDH_E001/NDH_EXTRACTION_PINS.json','NDH_TableInstalled.lean','NDH_Geometry.lean','NDH_Reference/Types.lean','NDH_Reference/Funs.lean','NDH_FRONTIER_BRIDGES.md','NDH_native.patch']:
  raw=subprocess.check_output(['git','show',rev+':'+p],cwd=R);assert len(raw)<=20*1024**2;q=E/'NEB_IMPORTED_SCALAR'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw);selected.append(dict(path=str(q.relative_to(R)),source_path=p,source_revision=rev,sha256=hashlib.sha256(raw).hexdigest()))
(E/'NEB_SCALAR_IMPORTS.json').write_text(json.dumps(dict(revision=rev,source='Immutable already-adopted NDH scalar/table packets; no live worktree access',files=selected),indent=1)+'\n');print('copied',len(selected),'immutable files')
