"""Generate structural type transport, with kernel-checked inverse laws.
Only NMT fresh types and canonical CurrentCompactCallerTypesV1 participate.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
raw=(E/'NNG_generated/NNG_verify_finish/Types.lean').read_text();ns='NNG_verify_finish';can='AspisR1PublicPreparation'
# Exclude Digest32 here: its contravariant method transport is separate.
items=[]
for m in re.finditer(r'^(structure|inductive) (\S+)([^\n]*)([\s\S]*?)(?=\n/--|\nend |\Z)',raw,re.M):
 kind,name,header,body=m.groups()
 if name not in {'aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.circle.SecureCirclePoint','aspis_core.state_only_prefix.r0.Challenges','r1_wire.SemanticTranscript','r1_semantic.Verified','r1_wire.Error','r1_wire.Prefix','r1_wire.ValidatedRecord'} and not name.startswith('aspis_statement.'):continue
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
 if ty.endswith(' H') and ty[:-2] in lookup:return f'{direction}{lookup[ty[:-2]]} ({x})'
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
prefix='''import NNG_verify_finish.Types
import NLJ_ObservedInitial
import NMT_TransportBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
'''
mods=[];prior='NNG_TransportBase';(E/(prior+'.lean')).write_text(prefix+'end AspisR1.NNG_Transport\n')
for kind,name,body,a in items:
 text='import '+prior+'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.NNG_Transport\nopen Aeneas Aeneas.Std\nopen AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)\n'
 generic=name in ['r1_wire.SemanticTranscript','r1_semantic.Verified']
 oldname=name.replace('aspis_statement.','').replace('aspis_core.state_only_prefix.r0.Challenges','r1_wire.Challenges')
 for direction,src,dst in [('to',ns,can),('from',can,ns)]:
  srcname=name if src==ns else oldname;dstname=name if dst==ns else oldname
  gen=' {H : Type}' if generic else '';app=' H' if generic else ''
  if kind=='structure':
   fields=re.findall(r'^  (\S+) :\s*([\s\S]*?)(?=\n  \S+ :|\Z)',body,re.M)
   assert fields,(name,body)
   args=[conv(ty,'x.'+f,direction) for f,ty in fields]
   text+=f'def {direction}{a}{gen} (x : {src}.{srcname}{app}) : {dst}.{dstname}{app} :=\n ⟨'+','.join(args)+'⟩\n'
  else:
   variants=re.findall(r'^\| (\w+) :([\s\S]*?)(?=\n\||\Z)',body,re.M)
   text+=f'def {direction}{a} : {src}.{srcname} → {dst}.{dstname}\n'
   for v,ty in variants:
    tys=[t.strip() for t in ty.split('→')][:-1];args=[f'x{i}' for i in range(len(tys))]
    text+=' | .'+v+(' '+' '.join(args) if args else '')+' => .'+v+(' '+' '.join('('+conv(t,x,direction)+')' for t,x in zip(tys,args)) if args else '')+'\n'
 # One type per smallest target; no concrete numerals are reduced.
 for direction,other,src in [('to','from',ns),('from','to',can)]:
  srcname=name if src==ns else oldname
  text+=f'@[simp] theorem {direction}{a}_inverse{gen} (x : {src}.{srcname}{app}) : {other}{a} ({direction}{a} x)=x := by\n cases x <;> simp [{direction}{a},{other}{a}]\n#print axioms {direction}{a}_inverse\n'
 text+='end AspisR1.NNG_Transport\n';mod='NNG_Transport_'+a;(E/(mod+'.lean')).write_text(text);mods.append(mod);prior=mod
(E/'NNG_TRANSPORT_TYPES.json').write_text(json.dumps(dict(modules=mods,types=[dict(name=n,alias=a)for k,n,b,a in items]),indent=1)+'\n')
