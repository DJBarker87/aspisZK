from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;dest=b.parent/'codex-cx-slice-s-compose3-cache-20261029/NEJ_final_objects_20261101'
dest.mkdir(parents=True,exist_ok=False);accepted={'NEJ_CommonFrame': 'b750fc64f27c537066f97c084c07465d3697a724d5ba8fe99cfb8609aa91c110', 'NEJ_ArrayFrame': '61a508417f431e8eb3b6279d5075ca53032f16ac53de9d83bff458fa580c999f', 'NEJ_ConcreteFrame': 'a9cbd66a3283dc82c5f308608e054723dc382b476db48d6d590efcb2d3a5e3c7', 'NEJ_WindowStep': '4b36d9098273881a6b5a42b1c23a060d01eed77f0a2c792b8a89cdc2e2f85f16', 'NEJ_CommonSourceFrame': 'b47b4335e548cecaf4c53ec951a98ba5d70c8366fbe726f29e3529d104ec7c9b', 'NEJ_ScannerFramed': 'a0f787cc3b3a5165b6adbe21b7faaa22218cbac4313d7fe76d7df2ee4353ff20', 'NEJ_ScannerWidth': '43655295246a20a4194a0af7355be32a419aec1b4e8dcdc08646f3044d47cd45', 'NEJ_Axioms': '50226e49bbcfb86057c6e203ecae1b26b838a739190875dc28752d61d638084c'};copied=[]
for module,expected in accepted.items():
 src=b/'NEJ_generated'/(module+'.lean');obj=b/'NEJ_objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
 for p in [src,obj]:
  q=dest/p.name;shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  copied.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
# Inventory only this job's scratch. Permanent caches and frozen inputs stay.
tmp=b/'NEJ_tmp';solver_files=[dict(path=str(p),bytes=p.stat().st_size) for p in tmp.rglob('*') if p.is_file()]
removed=[]
for name in ['NEJ_target','NEJ_objects','NEJ_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(copied=copied,solver_temp_inventory=solver_files,removed_only_own_rebuildable_scratch=removed,permanent_cache_retained=str(dest),frozen_lock_sha256=hashlib.sha256((b/'NEJ_src/Cargo.lock').read_bytes()).hexdigest())
(b/'NEJ_CACHE_FINAL.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(copied=len(copied),removed=removed)))
