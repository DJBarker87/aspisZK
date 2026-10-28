"""Type/import/namespace port of the owned V241 prefix; computation stays raw."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');raw=D/'raw224-prefix-resume3';record={}
for source,module in [('Types','PV_B3P_PrefixTypes224'),('Funs','PV_B3P_PrefixEmission224')]:
 s=(raw/(source+'.lean')).read_text();p=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
 p=p.replace('namespace PV_B3P_224\n','namespace PV_B3P_224Prefix\n').replace('end PV_B3P_224\n','end PV_B3P_224Prefix\n')
 p=re.sub(r'@\[discriminant (?:isize|usize|u8|u16|u32)\]\n','',p)
 p=re.sub(r'discriminant (?:isize|usize|u8|u16|u32),\s*','',p)
 if source=='Funs':
  p=p.replace('import PVB3P224Resume3ColumnRead.Types','import PV_B3P_PrefixTypes224')
  p=p.replace('31#i32','31#u32')
  assert p.count('Std.U64.wrapping_shr append_index level')==2
  p=p.replace('Std.U64.wrapping_shr append_index level','Std.U64.wrapping_shr append_index (UScalar.cast .U32 level)')
  p+='\n'+''.join('#print axioms PV_B3P_224Prefix.'+n+'\n' for n in re.findall(r'^def (\S+)',s,re.M))
  assert 'index_mut_back q' in p and 'index_mut_back1 weight' in p
  assert 'Array.update rows row_index' in p
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',p)
 (D/'lean'/(module+'.lean')).write_text(p)
 record[module]=dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),ported_sha256=hashlib.sha256(p.encode()).hexdigest())
record.update(computational_body_edits=False,edits=['Aeneas.Std/RustAttributes imports','private Types import and namespace separation','unsupported discriminant metadata only; order/payloads unchanged','positive31 shift literal types; U8 shift argument zero-extension to U32; native amount unchanged','axioms print commands'],generated_resource_options_preserved=True,
 write_fidelity={'tuple_value':'Array.update out i -> out1 -> cont(out1,i1)','side':'both borrowed values/weights restoration functions are applied in each branch before the entire row is written back; old immutable indexed value discarded, not its restoration','copy_rows':'producer side rows1 -> consumer side rows2 -> loop cont rows2; final output array retained'},
 scope='owned trace-view/registry-input prefix only; projection and fixed native registry source links pending; not a V241 or V245 closure')
(D/'port224-prefix-resume3.json').write_text(json.dumps(record,indent=2)+'\n')
