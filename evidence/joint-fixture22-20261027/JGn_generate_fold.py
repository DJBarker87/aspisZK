from pathlib import Path
import re,json,sys,runpy,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
g=runpy.run_path(str(P/'JGn_generate_copy_numeric.py'));add=g['add'];mul=g['mul'];Z=g['Z'];literal=g['literal'];high=g['high'];low=g['low'];patterns=g['patterns']
s=(R/'lean/FIq_Native12.lean').read_text()
pat=r'tag := (\d+)#u32,\s*weight_kind := (\d+)#u8,\s*weight_level := (\d+)#u8,\s*producer := \{ row := (\d+)#u16, slot := (\d+)#u8, pattern := (\d+)#u8 \},\s*consumer := \{ row := (\d+)#u16, slot := (\d+)#u8, pattern := (\d+)#u8 \}'
links=[list(map(int,x)) for x in re.findall(pat,s)];assert len(links)==136
rows={0:[[Z,Z] for _ in range(4)]};r=[[Z,Z] for _ in range(4)]
for i,(tag,kind,level,pr,ps,pp,cr,cs,cp) in enumerate(links):
 w=1 if kind in [0,1] else 0 if kind==2 else 1-((13>>level)&1) if kind==3 else ((13>>level)&1)
 for row,slot,patt,vf,wf in [(pr,ps,pp,0,1),(cr,cs,cp,2,3)]:
  selector=mul(high[row//16],low[row%16])
  r[vf][slot]=add(r[vf][slot],mul(selector,add((tag,0,0,0),patterns[patt])))
  r[wf][slot]=add(r[wf][slot],mul(selector,(w,0,0,0)))
 if (i+1)%8==0:rows[i+1]=[v.copy() for v in r]
def arr(v):return '⟨['+','.join(map(literal,v))+'],by rfl⟩'
data='''import JGn_CopyData
import FJk_CopyFullFold
import JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyRows
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
'''
data+='''def step := FJk_CopyStep.step (FIw_CopyEndpoint.modelSelectors JGl_NumericData.selectors)
  (decoded JGn_CopyData.patterns) JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index.val
  R0P.Variant.privateTransfer
'''
for n,row in rows.items():
 for f,v in zip(['pv','pw','cv','cw'],row):data+=f'def {f}{n:03} : Array field.QM31 2#usize := {arr(v)}\n'
 data+=f'def row{n:03} : R0P.CopyRowExtension K := FJk_CopyStep.row pv{n:03} pw{n:03} cv{n:03} cw{n:03}\n'
for k in range(17):data+=f'def block{k:02} : List R0P.CopyLink := (R0P.copyLinks.drop {8*k}).take 8\n'
data+='''theorem ext (x y : R0P.CopyRowExtension K)
    (hp : x.producerValues=y.producerValues) (hw : x.producerWeights=y.producerWeights)
    (hc : x.consumerValues=y.consumerValues) (hd : x.consumerWeights=y.consumerWeights) : x=y := by
  cases x
  cases y
  cases hp
  cases hw
  cases hc
  cases hd
  rfl
#print axioms ext
end AspisR1.JGn_CopyRows
end
'''
files={'JGn_CopyRows':data}
for k in range(17):
 mod=f'JGn_CopyChunk{k:02}';start=k*8;end=start+8
 t=f'''import JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open JGn_CopyRows
'''
 for short,field in [('pv','producerValues'),('pw','producerWeights'),('cv','consumerValues'),('cw','consumerWeights')]:
  for j in range(2):
   t+=f'''theorem {short}{j} : (block{k:02}.foldl step row{start:03}).{field} {j}=row{end:03}.{field} {j} := by
  jgl_words
#print axioms {short}{j}
'''
 t+=f'''theorem value : block{k:02}.foldl step row{start:03}=row{end:03} := by
  apply JGn_CopyRows.ext
'''
 for short in ['pv','pw','cv','cw']:t+=f'  · funext i\n    fin_cases i\n    · exact {short}0\n    · exact {short}1\n'
 t+='#print axioms value\nend AspisR1.'+mod+'\nend\n';files[mod]=t
for mod,t in files.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t,mod
 else:p.write_text(t)
if '--check' not in sys.argv:
 (P/'JGn_COPY_ROWS_INPUTS.json').write_text(json.dumps(dict(index=13,links=links,rows=rows,source_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2)+'\n')
print('copy row chunks checked' if '--check' in sys.argv else 'copy rows generated as eight-link symbolic word certificates; eight projections per chunk')
