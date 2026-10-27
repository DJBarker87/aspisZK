from pathlib import Path
import re,json,sys,hashlib
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
# Tiny 14x16 preflight, not a dense arithmetic release gate.
M=2147483647
Z=(0,0,0,0)
def add(x,y):return tuple((a+b)%M for a,b in zip(x,y))
def mul(x,y):
 def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M)
 p=cm(x[:2],y[:2]);q=cm(x[2:],y[2:]);r=cm(q,(2,1));s=cm(x[:2],y[2:]);t=cm(x[2:],y[:2])
 return ((p[0]+r[0])%M,(p[1]+r[1])%M,(s[0]+t[0])%M,(s[1]+t[1])%M)
def literal(w):return f'⟨⟨{w[0]}#u32,{w[1]}#u32⟩,⟨{w[2]}#u32,{w[3]}#u32⟩⟩'
cs=(R/'lean/JGl_NumericCanonical.lean').read_text()
def cells(n):
 t=cs.split('theorem '+n+' :')[1].split('#print axioms')[0]
 return [tuple(map(int,re.findall(r'(\d+)<2147483647',l))) for l in t.splitlines() if 'change (' in l]
a=cells('a');high=cells('high');low=cells('low')
lam=(399501241,284689285,1852519329,449773828)
powers=[];power=lam
for _ in range(16):powers.append(power);power=mul(power,lam)
src=(R/'lean/FIq_CopyPatterns.lean').read_text();patterns=[];descriptors=[]
for k in range(14):
 body=src.split(f'def pattern{k:02} :')[1].split('@[irreducible]')[0]
 def arr(n,nextn=None):
  text=body.split(n+' :=')[1]
  if nextn:text=text.split(nextn+' :=')[0]
  nums=list(map(int,re.findall(r'(\d+)#u(?:8|32)\b',text)))
  if 'Array.repeat' in text:return nums*16
  assert len(nums)==16,(k,n,nums)
  return nums
 kinds=arr('kinds','columns');columns=arr('columns','offsets');offsets=arr('offsets')
 total=Z
 for j in range(16):
  if kinds[j]==1:total=add(total,mul(powers[j],add(a[columns[j]],(offsets[j],0,0,0))))
 patterns.append(total);descriptors.append(dict(kinds=kinds,columns=columns,offsets=offsets))
data='import JGn_CopyPowers\nimport FJk_CopyRawValue\nimport FJk_ActiveValue\nimport FJk_PatternValuesRaw\nset_option autoImplicit false\nnamespace AspisR1.JGn_CopyData\nopen Aeneas Aeneas.Std FIq_Native\n'
data+='def patterns : Array field.QM31 14#usize := ⟨['+','.join(map(literal,patterns))+'],by rfl⟩\nend AspisR1.JGn_CopyData\n'
p=R/'lean/JGn_CopyData.lean'
if '--check' in sys.argv:assert p.read_text()==data
else:p.write_text(data)
manifest=dict(powers=powers,patterns=patterns,descriptors=descriptors,source_sha256=hashlib.sha256(src.encode()).hexdigest(),strategy='Symbolic original FJk source VALUE theorems; bounded per-pattern word certificates. No native loop reduction.')
if '--check' not in sys.argv:(P/'JGn_COPY_NUMERIC_INPUTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('copy numeric generator checked' if '--check' in sys.argv else 'copy numeric data generated')
# Persist the per-pattern kernel certificate shape and canonicality guard.
s='''import JGn_CopyData
import FJk_PatternRegistry
import JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_PatternMath
open FIw_ArrayValue (decoded)
'''
for i in range(14):
 s+=f'''theorem lane{i} : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨{i},by decide⟩=
    decoded JGn_CopyData.patterns ⟨{i},by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane{i}
'''
s+='''theorem value : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers=
    decoded JGn_CopyData.patterns := by
  funext i
  fin_cases i
'''+''.join(f'  · exact lane{i}\n' for i in range(14))+'#print axioms value\nend AspisR1.JGn_PatternMath\nend\n'
canonical='''import JGn_CopyData
import JGl_NumericCanonical
set_option autoImplicit false
namespace AspisR1.JGn_CopyCanonical
open FIw_ArrayValue (canonical)
theorem patterns : canonical JGn_CopyData.patterns := by
  apply JGl_NumericCanonical.fromCells
  intro i
  fin_cases i
'''
for a,b,c,d in patterns:canonical+=f'  · change ({a}<2147483647 ∧ {b}<2147483647) ∧ ({c}<2147483647 ∧ {d}<2147483647)\n    omega\n'
canonical+='#print axioms patterns\nend AspisR1.JGn_CopyCanonical\n'
for mod,body in [('JGn_PatternMath',s),('JGn_CopyCanonical',canonical)]:
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==body,mod
 else:p.write_text(body)
