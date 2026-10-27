"""Generate the 16 pinned constant quartet cells consumed by the fallback block.

--check validates bytes. Each cell proves four constant reads and its matrix
index, avoiding normalization of a SHA recurrence or symbolic round state.
"""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';out=root/'evidence/pv-cblib-20261027'
s=(out/'source/sha2-0.10.9__src__consts.rs').read_text();v=re.findall(r'0x[0-9a-f]+',s[s.index('pub const K32:'):s.index('pub const K32X4:')]);assert len(v)==64
vals=[str(int(x,16))+'#u32' for x in v]
texts={}
head='''import R1Z.PV_CBL_FallbackBlock
import R1Z.PV_CBL_FallbackConstants
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstantMatrix
set_option autoImplicit false
'''
body=''.join(f'def q{j} : Array U32 4#usize := PV_CBL_FallbackArray4.pack '+ ' '.join(vals[j*4:j*4+4][::-1])+'\n' for j in range(16))
body+='def matrix : Array (Array U32 4#usize) 16#usize := ⟨['+','.join(f'q{j}' for j in range(16))+'],by simp⟩\n'
body+='theorem words_source : PV_CBL_FallbackBlock.sha_fallback_consts.K32.val=PV_CBL_FallbackConstants.words := by\n  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32\n  rfl\n'
body+=''.join(f'#print axioms q{j}\n' for j in range(16))+'#print axioms matrix\n#print axioms words_source\n'
texts['PV_CBL_FallbackConstantMatrix']=head+body+'end R1Z.PV_CBL_FallbackConstantMatrix\n'
for j in range(16):
 name=f'PV_CBL_FallbackConstant{j:02}'
 s=f'''import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.{name}
set_option autoImplicit false
'''
 for k in range(4):
  i=j*4+k;s+=f'''theorem word{k} : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 {i}#usize = ok {vals[i]} := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
'''
 s+=f'''theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix {j}#usize =
    ok PV_CBL_FallbackConstantMatrix.q{j} := by
  rfl
'''
 s+=''.join(f'#print axioms word{k}\n' for k in range(4))+'#print axioms vector\n'+f'end R1Z.{name}\n';texts[name]=s
imports=''.join(f'import R1Z.PV_CBL_FallbackConstant{j:02}\n' for j in range(16))
s=imports+'''open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstantSource
set_option autoImplicit false
theorem source : PV_CBL_FallbackBlock.sha_fallback_consts.K32X4 =
    ok PV_CBL_FallbackConstantMatrix.matrix := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_consts.K32X4,
'''
s+=',\n'.join('    '+', '.join(f'PV_CBL_FallbackConstant{j:02}.word{k}' for k in range(4)) for j in range(16))+',\n    bind_tc_ok] <;> rfl\n#print axioms source\nend R1Z.PV_CBL_FallbackConstantSource\n'
texts['PV_CBL_FallbackConstantSource']=s
for name,txt in texts.items():
 p=b/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==txt,name
 else:p.write_text(txt)
(out/'fallback-constant-chunks.json').write_text(json.dumps(dict(status='PASS',source_sha256=hashlib.sha256((out/'source/sha2-0.10.9__src__consts.rs').read_bytes()).hexdigest(),files={n:hashlib.sha256(t.encode()).hexdigest() for n,t in texts.items()},scope='16 source macro constant quartets; no concrete SHA round state'),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(texts),'modules')
