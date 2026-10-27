from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]; P=2147483647

def wide(w):return '⟨⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩,⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩⟩'%tuple(w)
def cmul(x,y):return [(x[0]*y[0]-x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P]
def add(x,y):return [(a+b)%P for a,b in zip(x,y)]
def qmul(x,y):
 a=cmul(x[:2],y[:2]);b=cmul(x[2:],y[2:]);r=cmul([2,1],b)
 return add(a,r)+add(cmul(x[:2],y[2:]),cmul(x[2:],y[:2]))
def mul(x,y):
 a=qmul(x[:4],y[:4]);b=qmul(x[4:],y[4:]);u=cmul([2,1],b[2:])+b[:2]
 return add(a,u)+add(qmul(x[:4],y[4:]),qmul(x[4:],y[:4]))
def nums(mod,definition):
 t=(R/f'lean/{mod}.lean').read_text(); d=re.search(rf'def {definition}[^\n]*:= (.*)',t).group(1)
 return list(map(int,re.findall(r'(\d+)#u32',d)))
def scalar(mod):
 t=(R/f'lean/{mod}.lean').read_text(); d=re.search(r'def bytes[^\n]*:= \[(.*?)\]',t).group(1)
 b=bytes(map(int,re.findall(r'(\d+)#u8',d)));return [int.from_bytes(b[k:k+4],'little') for k in range(0,32,4)]

def generate():
 out={}; results=[]
 for r in range(2):
  alpha=scalar(f'JFq_Alpha{r}')
  a=[0]*8
  for step in range(7):
   i=6-step;c=nums(f'JGo_TX2_Cell{r}_{i}','value');product=mul(a,alpha);z=add(product,c)
   mod=f'JGo_TX2_Horner{r}_{step}'
   s=f'''import FIn_ExtractInstall
import JGo_TX2_Cell{r}_{i}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
abbrev E := AspisR1Stage2.Stage2Finish.E
def before : E := {wide(a)}
def alpha : E := {wide(alpha)}
def product : E := {wide(product)}
def after : E := {wide(z)}
theorem multiply : FIn_Polynomial.mul before alpha=ok product := by with_unfolding_all rfl
#print axioms multiply
theorem addition : FIn_Primitives.add product JGo_TX2_Cell{r}_{i}.value=ok after := by with_unfolding_all rfl
#print axioms addition
end AspisR1.{mod}
end
'''
   out[mod+'.lean']=s;a=z
  results.append(a)
 return out,results
mods,results=generate()
for f,s in mods.items():
 p=R/'lean'/f
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('final Horner values',results)
