from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;dest=b.parent/'codex-cx-slice-s-compose6-cache-20261029/NEQ_final_objects_20261103'
dest.mkdir(parents=True,exist_ok=False);accepted={'NEQ_ImportAudit': '6ea754c05358b660136248f407e0964907b3f537ce9423c6a466977952dff028', 'NEQ_LateBorrow': '825eb450e231acb5e634515cdff12218139df06e854371f119ee3cf39e3fa630', 'NEQ_EncoderOracle': '1541d8f63a6632009d9af14bb951e26cc03cfc37e8abfc3379d2b976592276c1', 'NEQ_RootFrame': '69f716ecd71b9b1800265860dc827c763ee229a48c0b94cfb8ab5338a39d46fb', 'NEQ_EncoderDomains': '12a6987c186de93d814f1542822f8b348da5f2e3ff448698f8ffe88e034426b9', 'NEQ_ResultValidator': '5e4c4901fb967baab573f7769975fc5cad3810e5c6c11b8c181c2a596cf1e8ba', 'NEQ_NullifierDomains': '342985ce1f5a7c884c5e15690419e4078b6f3366e30a5b416631768cb6f90233', 'NEQ_DecodeScalar': '061ddec6b78ff9d6a4caa2b74a79e680ea9ffc64aa8f3a8a25620ac9717021c8', 'NEQ_ParserCanonical': 'bc61957aa44b016a878f1ef7581414717e89eeb4ea7c6e17bfc41792f5790af4', 'NEQ_UnwrapDomains': 'f1ff61b794fa4753909d00ee454be689a2bfbdfd48438f79a6783db72ec8e19a', 'NEQ_CommonDecode': '639d791a37a5b4fa193edff5c867128db954e962a61f94d57d6e50134899fbc5', 'NEQ_PaymentDecode': '61c3c6780f9ba6712b92f4af9c0b3c373a2e4d84bcab7b0f2827b000261fdc7a', 'NEQ_BorrowWidth': '5feeee3567392505f07fafdb440c25b22547d6af48a699030007d26c279a3baa', 'NEQ_PaymentDomains': 'fd01df40c04ad74592d748b5da7c48da2aebc22a6e714ec5e1490e798c0e9289', 'NEQ_FinalAudit': '36c8f4f17a8d553d29f24515b13dcc2410d05b0ca272ce833d86fc2b9e8284af'};copied=[]
for module,expected in accepted.items():
 src=b/'NEQ_generated'/(module+'.lean');obj=b/'NEQ_objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==expected
 for p in [src,obj]:
  q=dest/p.name;shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  copied.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
# Inventory only this job's scratch. Permanent caches and frozen inputs stay.
tmp=b/'NEQ_tmp';solver_files=[dict(path=str(p),bytes=p.stat().st_size) for p in tmp.rglob('*') if p.is_file()]
removed=[]
for name in ['NEQ_target','NEQ_objects','NEQ_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(copied=copied,solver_temp_inventory=solver_files,removed_only_own_rebuildable_scratch=removed,permanent_cache_retained=str(dest),frozen_lock_sha256=hashlib.sha256((b/'NEQ_src/Cargo.lock').read_bytes()).hexdigest())
(b/'NEQ_CACHE_FINAL.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(copied=len(copied),removed=removed)))
