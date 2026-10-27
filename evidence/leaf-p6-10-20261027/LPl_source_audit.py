from pathlib import Path
import subprocess,hashlib,json,tempfile,re
E=Path(__file__).resolve().parent;root=E.parent.parent;release='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mp=json.loads((root/'evidence/leaf-p6-3-20261027/LPc_INPUTS/LPc_input-map.json').read_text())
patches=[root/'evidence/leaf-p6-1-20261027/LPa_kani_harness.patch',root/'evidence/leaf-p6-3-20261027/LPc_INPUTS'/mp['LPc_K020']['patch'],root/'evidence/leaf-p6-7-20261027/LPg_K030-harness.patch',root/'evidence/leaf-p6-8-20261027/LPh_K030-harness.patch',E/'LPl_K004-harness.patch']
files=set()
for p in patches:
 files.update(re.findall(r'^\+\+\+ b/(.+)$',p.read_text(),re.M))
checks={}
with tempfile.TemporaryDirectory(prefix='LPl_patch_') as td:
 d=Path(td)
 for rel in files:
  s=subprocess.run(['git','show',release+':'+rel],cwd=root,capture_output=True)
  if s.returncode==0:
   q=d/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(s.stdout)
 for patch in patches:
  r=subprocess.run(['git','apply',str(patch)],cwd=d,capture_output=True,text=True)
  if r.returncode:raise RuntimeError(str(patch)+'\n'+r.stderr)
 base=json.loads((E/'LPl_source-provenance.json').read_text())
 # Validate patched inputs directly against exact Kani snapshots, with later
 # owned harness content pinned by the final committed patch.
 receipt=json.loads((E/'LPl_K004/receipt.json').read_text())
 for name,sha in receipt['source_hashes'].items():
  rel=name.removeprefix('LPl_src/');p=d/rel
  actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else base['manifest'].get(rel)
  assert actual==sha,(rel,actual,sha)
  checks[rel]=sha
 frozen={}
 for rel in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','Cargo.lock']:
  s=subprocess.check_output(['git','show',release+':'+rel],cwd=root)
  frozen[rel]={'sha256':hashlib.sha256(s).hexdigest(),'bytes':len(s)}
 for tree in ['crates','programs','Cargo.lock']:
  assert subprocess.check_output(['git','rev-parse',release+':'+tree],cwd=root)==subprocess.check_output(['git','rev-parse','HEAD:'+tree],cwd=root)
  assert subprocess.run(['git','diff','--quiet','--',tree],cwd=root).returncode==0
 body='fn echeck(b:&[u8],k:bool)->Result<(),Error> {\n    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}\n    Ok(())\n}'
 source=subprocess.check_output(['git','show',release+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=root).decode()
 assert body in source and body in (d/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
 out={'frozen_revision':release,'frozen_inputs':frozen,'ordered_patch_reconstruction':[{'path':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in patches],'matched_native_inputs':checks,'echeck_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'echeck_body_verbatim':True,'source_association':{'loop':'chunks_exact32 source loop equals Trace next/reject/done cases','local_decoder':'K001 all32 bytes and both k; L023 polynomial/window carrier join','cursor':'K002 exact pointer/count for0..29 of arbitrary928 backing; L024 read/advance','native_result':'K003 exact Ok/Parse; L026 complete Trace result and uniqueness','nonvacuity':'K004 native fixtures; L027 Lean fixtures/empty result; L026 total trace existence'},'shipped_trees_unchanged':True}
(E/'LPl_SOURCE.json').write_text(json.dumps(out,indent=2)+'\n');print('Ordered patches and',len(checks),'native inputs match; echeck body frozen')
