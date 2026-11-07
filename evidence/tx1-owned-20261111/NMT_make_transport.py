"""Generate structural type transport, with kernel-checked inverse laws.
Only NMT fresh types and canonical CurrentCompactCallerTypesV1 participate.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
raw=(E/'NMT_tx1.Types.lean').read_text();ns='NMT_tx1';can='AspisR1CurrentCaller'
# Exclude Digest32 here: its contravariant method transport is separate.
items=[]
for m in re.finditer(r'^(structure|inductive) (\S+)([^\n]*)([\s\S]*?)(?=\n/--|\nend |\Z)',raw,re.M):
 kind,name,header,body=m.groups()
 if name=='aspis_core.digest.Digest32':continue
 alias='T'+str(len(items));items.append((kind,name,body,alias))
lookup={n:a for k,n,b,a in items}
def conv(ty,x,direction):
 ty=' '.join(ty.split()).strip()
 while ty.startswith('(') and ty.endswith(')'):
  depth=0;full=True
  for i,c in enumerate(ty):
   depth+=(c=='(')-(c==')')
   if depth==0 and i<len(ty)-1:full=False;break
  if not full:break
  ty=ty[1:-1].strip()
 if ty in lookup:return f'{direction}{lookup[ty]} ({x})'
 for ctor,helper in [('Array ','arr'),('alloc.vec.Vec ','vec')]:
  if ty.startswith(ctor):
   rest=ty[len(ctor):];elem=rest
   if ctor=='Array ':
    if rest.startswith('('):
     depth=0
     for i,c in enumerate(rest):
      depth+=(c=='(')-(c==')')
      if depth==0:elem=rest[:i+1];break
    else:elem=rest.split()[0]
   inner=conv(elem,'z',direction)
   if inner=='z':return x
   return f'{helper} (fun z => {inner}) ({x})'
 return x
prefix='''import NMT_tx1.Types
import CurrentCompactCallerTypesV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std

def arr {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
 ⟨x.val.map f, by simpa using x.property⟩
def vec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨x.val.map f, by simpa using x.property⟩
theorem list_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : List A) : (xs.map f).map g=xs := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.map_cons,inverse,ih]
#print axioms list_inverse
@[simp] theorem arr_inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : Array A n) : arr g (arr f xs)=xs := by
 cases xs
 simp only [arr, list_inverse f g inverse]
@[simp] theorem vec_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : alloc.vec.Vec A) : vec g (vec f xs)=xs := by
 cases xs
 simp only [vec, list_inverse f g inverse]
#print axioms arr_inverse
#print axioms vec_inverse
'''
mods=[];prior='NMT_TransportBase';(E/(prior+'.lean')).write_text(prefix+'end AspisR1.NMT_Transport\n')
for kind,name,body,a in items:
 text='import '+prior+'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.NMT_Transport\nopen Aeneas Aeneas.Std\n'
 for direction,src,dst in [('to',ns,can),('from',can,ns)]:
  if kind=='structure':
   fields=re.findall(r'^  (\S+) :\s*([\s\S]*?)(?=\n  \S+ :|\Z)',body,re.M)
   assert fields,(name,body)
   args=[conv(ty,'x.'+f,direction) for f,ty in fields]
   text+=f'def {direction}{a} (x : {src}.{name}) : {dst}.{name} :=\n ⟨'+','.join(args)+'⟩\n'
  else:
   variants=re.findall(r'^\| (\w+) :([\s\S]*?)(?=\n\||\Z)',body,re.M)
   text+=f'def {direction}{a} : {src}.{name} → {dst}.{name}\n'
   for v,ty in variants:
    tys=[t.strip() for t in ty.split('→')][:-1];args=[f'x{i}' for i in range(len(tys))]
    text+=' | .'+v+(' '+' '.join(args) if args else '')+' => .'+v+(' '+' '.join('('+conv(t,x,direction)+')' for t,x in zip(tys,args)) if args else '')+'\n'
 # One type per smallest target; no concrete numerals are reduced.
 for direction,other,src in [('to','from',ns),('from','to',can)]:
  text+=f'@[simp] theorem {direction}{a}_inverse (x : {src}.{name}) : {other}{a} ({direction}{a} x)=x := by\n cases x <;> simp [{direction}{a},{other}{a}]\n#print axioms {direction}{a}_inverse\n'
 text+='end AspisR1.NMT_Transport\n';mod='NMT_Transport_'+a;(E/(mod+'.lean')).write_text(text);mods.append(mod);prior=mod
(E/'NMT_TRANSPORT_TYPES.json').write_text(json.dumps(dict(modules=mods,types=[dict(name=n,alias=a)for k,n,b,a in items]),indent=1)+'\n')
