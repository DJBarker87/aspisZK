from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;dest=b.parent/'codex-cx-slice-s-compose5-cache-20261029/NEM_final_objects_20261102'
dest.mkdir(parents=True,exist_ok=False);accepted={'NEM_DigestInstance': 'eafeac190fab6dde7de40b6e6eb050a759308b77c755d072a15616b3164fad5d', 'NEM_PaymentReached': 'd084e0820842bc6cdc5beb53bb0f6c34720e6ea7b94f7665750c301f31071b03', 'NEM_PaymentFrame': '6d844a1f0cae4ee00151e356ef34ccea5c8ce8707465a6288805a8cf5ba00f03', 'NEM_LaneReached': '5cb0548db9471caa03a9f93b3e1658bfd749d582b00dbb47074c88305e7d2cec', 'NEM_FrontierValidatorInstance': '52bccecabc26841e0be64f81fb2ad60fe30795c4490612401b3e881a3b6bb8de', 'NEM_EncoderFrame': '8b386b9eaa025dd68843b6610661e54c7932524737ee668c211a890c097d391c', 'NEM_BorrowAudit': '894905a8f9822f73f7d8f8b3c4d34668b90e4d44f570b3d18d7e313275fc996d', 'NEM_SnapshotBorrow': '7377c5d73d6c0f06613c980fc54477643d80076931226ac7717462e9a39e3436', 'NEM_LateOracle': 'f5f0f082a22b59c52a479e46bbada9235d13f610ed878d90c45c965fae9e09d9', 'NEM_ArraySnapshotView': '5d79335e2995901146a4a5b596827665f98630eb04712b365b679c7dc2d1ee0b', 'NEM_ValidatorComposed': '48d1cb4b7b7e42ebabe5c0aab87f7d2c7d4d2c715bc63037c90a39e9252a0456', 'NEM_KindInstance': '4f5bfaa24352d0ae91125885738e43b1f9582a7f09542bd2e06325c3005214b6', 'NEM_EncoderReceiver': '9426a12b3a3ca2f6cfa26de2640fefc0bb1b7e67493aae898ec7c92009fba7a9', 'NEM_FinalAudit': '4a326851b033351301466c4f8f8803f39aa6622ad2e21f181ee3f1c485e8d548'};copied=[]
for module,expected in accepted.items():
 src=b/'NEM_generated'/(module+'.lean');obj=b/'NEM_objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
 for p in [src,obj]:
  q=dest/p.name;shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  copied.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
# Inventory only this job's scratch. Permanent caches and frozen inputs stay.
tmp=b/'NEM_tmp';solver_files=[dict(path=str(p),bytes=p.stat().st_size) for p in tmp.rglob('*') if p.is_file()]
removed=[]
for name in ['NEM_target','NEM_objects','NEM_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(copied=copied,solver_temp_inventory=solver_files,removed_only_own_rebuildable_scratch=removed,permanent_cache_retained=str(dest),frozen_lock_sha256=hashlib.sha256((b/'NEM_src/Cargo.lock').read_bytes()).hexdigest())
(b/'NEM_CACHE_FINAL.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(copied=len(copied),removed=removed)))
