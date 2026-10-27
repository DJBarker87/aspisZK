"""Verify exact accepted method cuts against retained baseline emission."""
from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/continued'
rows=[]
for rawfile,names,mod in [
 ('Offpath-Funs.lean.txt',['def zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut','def zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut'],'PDict_OffpathBorrow'),
 ('Offpath-Funs.lean.txt',['def\n  digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks'],'PDict_CtUpdate'),
 ('CtConstructor-Funs.lean.txt',['def\n  digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default'],'PDict_CtConstructor')]:
 raw=(e/rawfile).read_text();out=(p/(mod+'.lean')).read_text()
 for name in names:
  a=raw.index(name);b=raw.index('\n/--',a);s=raw[a:b]
  if mod=='PDict_OffpathBorrow':s=s.replace(name,'def derefMut' if 'deref_mut' in name else 'def asMut')
  else:
   s=s.replace(name,'def updateBlocks' if mod=='PDict_CtUpdate' else 'def construct').replace('digest.core_api.VariableOutputCore T','@digest.core_api.VariableOutputCore (native base) T').replace('digest.core_api.ct_variable.CtVariableCoreWrapper T','PDict_CryptoTypes.digest.core_api.ct_variable.CtVariableCoreWrapper T').replace('generic_array.GenericArray Std.U8','PDict_CryptoTypes.generic_array.GenericArray Std.U8').replace('typenum.uint.UInt','PDict_UInt.typenum.uint.UInt').replace('  := do\n','  :=\n  letI : ExternalTypes := native base\n  do\n')
   s=s.replace('  let t ←\n    core.result.Result.unwrap digest.InvalidOutputSize.Insts.CoreFmtDebug r','  let t ← match r with\n    | .Ok value => .ok value\n    | .Err _ => .fail .panic')
  assert s in out,(mod,name)
 rows.append(dict(module=mod,source_sha256=hashlib.sha256(out.encode()).hexdigest(),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),changes='Renaming and concrete carrier qualifications only; ctor additionally delta-reduces existing std unwrap to erase its unused Debug argument, no formatter axiom selected'))
(e/'source-normalization.json').write_text(json.dumps(rows,indent=2)+'\n');print('checked',len(rows),'cuts')
