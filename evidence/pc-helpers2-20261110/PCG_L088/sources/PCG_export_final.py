from pathlib import Path
import json,hashlib,shutil,re,lzma
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-pc-helpers2-cache-20261110');D=C/'PCG_exports_20261110';D.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
todo=['PCG_COMBINED_IMPORT'];seen=set();files=[]
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);rel=Path(m.replace('.','/'));src=B/'PCG_generated'/rel.with_suffix('.lean') if '.' not in m else B/'PCG_generated'/Path(m.replace('.','/')+'.lean')
 # Module dots are path separators, never filesystem suffixes.
 src=B/'PCG_generated'/Path(m.replace('.','/')+'.lean');assert src.is_file(),str(src)
 for child in re.findall(r'^import (PCG_\S+)',src.read_text(),re.M):todo.append(child)
 obj=B/'PCG_objects'/Path(m.replace('.','/')+'.olean');assert obj.is_file(),str(obj)
 for f,target in [(src,D/Path(m.replace('.','/')+'.lean'))]+[(f,D/f.relative_to(B/'PCG_objects')) for f in [obj,*obj.parent.glob(obj.name+'.*')]]:
  target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert sha(target)==sha(f),'never overwrite a different retained export'
  else:shutil.copyfile(f,target)
  files.append(dict(module=m,path=str(target),source=str(f),sha256=sha(target),bytes=target.stat().st_size))
manifest=dict(export=str(D),base_cache=str(C),LEAN_PATH=[str(D),str(C)],modules=sorted(seen),files=files,imports_manifest_sha256=sha(B/'PCG_IMPORTS.json.xz'),native_status='REPAIRED_PCG_F1',gate_attempts=['PCG_L080','PCG_L081',*['PCG_L'+str(n) for n in range(82,88)]],binary_sha256='728c8fe68a7254ef77ea163aa8ac8f82b5f876abd1b8b79e1fb5077d762722f0')
(B/'PCG_EXPORT_MANIFEST.json').write_text(json.dumps(manifest,indent=1)+'\n');(D/'PCG_EXPORT_MANIFEST.json').write_text(json.dumps(manifest,indent=1)+'\n')
print('Final own export copied and hashed: '+str(len(seen))+' modules, '+str(len(files))+' files')
