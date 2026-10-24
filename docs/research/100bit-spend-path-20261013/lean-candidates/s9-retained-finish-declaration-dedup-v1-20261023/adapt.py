from pathlib import Path
import hashlib,json,re,sys
CHECK="--check" in sys.argv
W=Path(__file__).resolve().parent
S=W/'original'
R=W/'shared-owner'
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=[]
for file,decl,next_decl,owner in [('Types.lean','canonical.Q','canonical.Dot','Types.lean'),('Funs.lean','canonical.P','canonical.reduce','Funs.lean')]:
 b=(S/'AspisR1CanonicalDotFinish'/file).read_bytes();s=b.decode();o=(R/owner).read_bytes().decode()
 if decl=='canonical.Q':
  body='@[reducible]\ndef canonical.Q := Array Std.U32 4#usize'
  assert body in s and body in o
  start=s.index('/-- [aspis_r1_stage2_adopted_caller::canonical::Q]');end=s.index('/-- [aspis_r1_stage2_adopted_caller::canonical::Dot]')
  imp='import AspisR1CanonicalQRaw.Types\n'
 else:
  body='@[global_simps, irreducible] def canonical.P : Std.U32 := 2147483647#u32'
  assert body in s and body in o
  start=s.index('/-- [aspis_r1_stage2_adopted_caller::canonical::P]');end=s.index('/-- [aspis_r1_stage2_adopted_caller::canonical::reduce]')
  imp='import AspisR1CanonicalQRaw.Funs\n'
 removed=s[start:end];anchor='import Aeneas\n';assert s.count(anchor)==1
 adapted=(s[:start]+s[end:]).replace(anchor,anchor+imp,1)
 # Exact inverse: remove single added owner import and restore the original span.
 before_import=adapted.replace(imp,'',1);inv=before_import[:start]+removed+before_import[start:]
 assert inv.encode()==b
 p=W/'sources/AspisR1CanonicalDotFinish'/file;p.parent.mkdir(parents=True,exist_ok=True);assert p.read_text()==adapted if CHECK else True
 if not CHECK:p.write_text(adapted)
 manifest.append({'declaration':decl,'input_path':str(S/'AspisR1CanonicalDotFinish'/file),'input_sha256':sha(b),'shared_owner_path':str(R/owner),'shared_owner_sha256':sha(o.encode()),'identical_typed_declaration':body,'typed_declaration_sha256':sha(body.encode()),'removed_span':removed,'removed_offset':start,'added_owner_import':imp,'output_sha256':sha(adapted.encode()),'inverse_exact':True})
for name in ['CanonicalDotReduceSemantics.lean','CanonicalDotFinishSemantics.lean']:
 b=(S/name).read_bytes();q=W/'sources'/name
 if CHECK:assert q.read_bytes()==b
 else:q.write_bytes(b)
 manifest.append({'unchanged_source':name,'sha256':sha(b)})
if not CHECK:(W/'adapter-pins.json').write_text(json.dumps({'schema':'nominal-declaration-dedup-adapter-v1','changes':manifest,'scope':'Only shared-owner imports plus removal of byte-identical typed Q/P duplicate declarations and their associated docs. All remaining bytes and mathematical statements unchanged; inverse exact.'},indent=2)+'\n')
print(json.dumps({'targets':4,'deduplicated_declarations':2,'inverse_exact':True}))
