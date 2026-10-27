from pathlib import Path
import re,json,sys,runpy
P=Path(__file__).resolve().parent;R=P.parents[1]
g=runpy.run_path(str(P/'JGn_generate_copy_numeric.py'));add=g['add'];mul=g['mul'];Z=g['Z'];literal=g['literal'];high=g['high'];low=g['low']
s=(R/'docs/research/v8-r0-sem-proof-20261008/lean/R0P/CopyConstants.lean').read_text()
masks=list(map(int,re.findall(r'\d+',s.split('def copyActiveRowMasks :')[1].split(':= ![')[1].split(']')[0])));assert len(masks)==64
partials=[Z];v=Z
for i,m in enumerate(masks):
 complement=m.bit_count()>8;selected=m^65535 if complement else m
 total=(1,0,0,0) if complement else Z
 for j in range(16):
  if selected>>j&1:total=add(total,tuple(-x%g['M'] for x in low[j]) if complement else low[j])
 if m:v=add(v,mul(high[i],total))
 if (i+1)%8==0:partials.append(v)
assert v==(766140686,1850622266,1931269867,1348309306)
s='''import JGn_CopyData
import JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_ActiveData
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (decode)
'''
for n,q in enumerate(partials):s+=f'def a{n*8:02} : field.QM31 := {literal(q)}\n'
for k in range(8):s+=f'def block{k} : List (Fin 64) := (FJk_ActiveValue.indices.drop {k*8}).take 8\n'
s+='end AspisR1.JGn_ActiveData\nend\n'
files={'JGn_ActiveData':s}
s='''import JGn_ActiveData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_ActiveMath
open FIv_NativeValue (decode)
open JGn_ActiveData
'''
for k in range(8):s+=f'''theorem chunk{k} : block{k}.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a{k*8:02})=
    decode a{(k+1)*8:02} := by
  jgl_words
#print axioms chunk{k}
'''
s+='''attribute [local irreducible] List.foldl FJk_ActiveValue.step
theorem value : FJk_ActiveValue.model JGl_NumericData.selectors 0 0=decode a64 := by
  have layout : FJk_ActiveValue.indices=block0++block1++block2++block3++block4++block5++block6++block7 := by rfl
  unfold FJk_ActiveValue.model
  rw [List.drop_zero,layout]
  change ((block0++block1++block2++block3++block4++block5++block6++block7).foldl
    (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a00))=decode a64
  simp only [List.foldl_append]
  rw [chunk0,chunk1,chunk2,chunk3,chunk4,chunk5,chunk6,chunk7]
#print axioms value
end AspisR1.JGn_ActiveMath
end
'''
files['JGn_ActiveMath']=s
for m,t in files.items():
 p=R/'lean'/(m+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t,m
 else:p.write_text(t)
if '--check' not in sys.argv:(P/'JGn_ACTIVE_INPUTS.json').write_text(json.dumps(dict(masks=masks,partials=partials),indent=2)+'\n')
print('active chunks checked' if '--check' in sys.argv else 'active mask chunks generated')
