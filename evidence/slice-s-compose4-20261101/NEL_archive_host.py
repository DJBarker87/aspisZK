from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;dest=b.parent/'codex-cx-slice-s-compose3-cache-20261029/NEL_final_objects_20261102'
dest.mkdir(parents=True,exist_ok=False);accepted={'NEL_GetterAudit': '13f34fd18f9d2034096dbc405153aae3fe7ee1d3b605ed8d7fccc7a5ce385ed4', 'NEL_CopyArrayLaw': '13caf02cea6dfa336e0f3c3f5de434570ce3966ded1ae4078593d7f1e098a4bb', 'NEL_IterationAudit': '142819b82eb1c1484e97ab346e5d00d5e6b676874d2c55b744c1edaa41ec941f', 'NEL_DigestGeometry': '93c9e83218e686b3397caaf579d1831a3573b869efaeff3a69096067c8352a86', 'NEL_PaymentDomains': '73e4f42c45537e18b7e1dd49751aac74c7e63bb81b03db4731ea17b33c24e83b', 'NEL_SliceCopyLaw': '58d43676a3a3a5b1ef84ca6a8cdabf6ec555f0a6f01f9632242a21cb0a5325ce', 'NEL_OrderedWrites': 'a941692294be2c58176a7e10d934812775651ea6abfe3bb9dce0623d54a83f8a', 'NEL_CommonOracle': '199f8e0d369c897714c1615b6ec8f0d3c4510b124d579eb619e47cc55aa84df7', 'NEL_PaymentFieldCarriers': 'a88374995679d45fd133432da0535fda5b50f71bf7eeab9d98c570922a703229', 'NEL_PaymentOracle': '44d8285288214430ad6218daab5e79e4b42f29d07596be2786ce2e3c60a3a6de', 'NEL_FrontierGeometry': '2837e5538d613f1434fe6f061cb13ac71c6669a1542143e41e2d8161b51329bd', 'NEL_DigestLoopFrame': 'bdfaa2c16a7045026be10122ab18d5cd53c9f54ae2fbfc547b4d2eff31e0a58c', 'NEL_LateDomains': '974ac68a523557023b3c7a939f3fbccb19b537c9e31e56f20dd9e7a65254f7ba', 'NEL_FinalAudit': 'c8e763704e348c1f0f6c791cb89d09af9a557ae97ed3df86a925133d88e84731'};copied=[]
for module,expected in accepted.items():
 src=b/'NEL_generated'/(module+'.lean');obj=b/'NEL_objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
 for p in [src,obj]:
  q=dest/p.name;shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  copied.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
# Inventory only this job's scratch. Permanent caches and frozen inputs stay.
tmp=b/'NEL_tmp';solver_files=[dict(path=str(p),bytes=p.stat().st_size) for p in tmp.rglob('*') if p.is_file()]
removed=[]
for name in ['NEL_target','NEL_objects','NEL_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(copied=copied,solver_temp_inventory=solver_files,removed_only_own_rebuildable_scratch=removed,permanent_cache_retained=str(dest),frozen_lock_sha256=hashlib.sha256((b/'NEL_src/Cargo.lock').read_bytes()).hexdigest())
(b/'NEL_CACHE_FINAL.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(copied=len(copied),removed=removed)))
