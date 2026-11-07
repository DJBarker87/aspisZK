from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
raw=(E/'NMT_stage1_owned.Types.lean').read_text()
items=[]
for m in re.finditer(r'^(structure|inductive) (\S+)([^\n]*)([\s\S]*?)(?=\n/--|\nend |\Z)',raw,re.M):
 kind,name,header,body=m.groups()
 if not name.startswith('aspis_statement.'):continue
 items.append((kind,name,body))
plans=[]
for label,can,exclude,imports in [
 ('Dec','AspisR1TerminalDecoder',{'aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public'},['NFY_Part058']),
 ('Prep','AspisR1PublicPreparation',set(),['NJB_SemanticPublic']),
 ('First','NMT_first',set(),['NMT_first.Types']),
 ('FIq','FIq_Native',{'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1','aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1'},['NKR_DigestChildren','NKR_TermPublic'])]:
 # Only statement value types needed by semantic_public on prep/first; errors
 # are transported on the decoder path once, not duplicated needlessly.
 selected=[(k,n,b) for k,n,b in items if n not in exclude and (label=='Dec' or 'Error' not in n)]
 lookup={n:f'T{i}'for i,(k,n,b)in enumerate(selected)}
 def cname(n):return can+'.'+(n.removeprefix('aspis_statement.') if label!='First' else n)
 def conv(ty,x,d):
  ty=' '.join(ty.split()).strip()
  while ty.startswith('(') and ty.endswith(')'):
   level=0;full=True
   for i,c in enumerate(ty):
    level+=(c=='(')-(c==')')
    if level==0 and i<len(ty)-1:full=False;break
   if not full:break
   ty=ty[1:-1].strip()
  if ty in lookup:return f'{d}{lookup[ty]} ({x})'
  if ty.startswith('Array '):
   rest=ty[6:];elem=rest.split()[0]
   if rest.startswith('('):
    level=0
    for i,c in enumerate(rest):
     level+=(c=='(')-(c==')')
     if level==0:elem=rest[:i+1];break
   inner=conv(elem,'z',d)
   if inner!='z':return f'AspisR1.NMT_Transport.arr (fun z => {inner}) ({x})'
  return x
 prior='NMT_345TransportBase'
 for i,(kind,n,body) in enumerate(selected):
  alias=lookup[n];mod=f'NMT_345{label}_{alias}'
  t='import '+prior+'\n'+''.join('import '+v+'\n'for v in imports)+f'''set_option autoImplicit false
noncomputable section
namespace NMT_345{label}
open Aeneas Aeneas.Std AspisR1.NMT_Transport
'''
  for d,src,dst in [('to','NMT_stage1_owned.'+n,cname(n)),('from',cname(n),'NMT_stage1_owned.'+n)]:
   if kind=='structure':
    fields=re.findall(r'^  (\S+) :\s*([\s\S]*?)(?=\n  \S+ :|\Z)',body,re.M)
    assert fields,n
    t+=f'def {d}{alias} (x : {src}) : {dst} :=\n ⟨'+','.join(conv(ty,'x.'+f,d) for f,ty in fields)+'⟩\n'
   else:
    t+=f'def {d}{alias} : {src} → {dst}\n'
    for v,ty in re.findall(r'^\| (\w+) :([\s\S]*?)(?=\n\||\Z)',body,re.M):
     tys=[a.strip()for a in ty.split('→')][:-1];args=[f'x{j}'for j in range(len(tys))]
     t+=' | .'+v+(' '+' '.join(args)if args else '')+' => .'+v+(' '+' '.join('('+conv(ty,x,d)+')'for ty,x in zip(tys,args))if args else '')+'\n'
  for d,other,ty in [('to','from','NMT_stage1_owned.'+n),('from','to',cname(n))]:
   t+=f'@[simp] theorem {d}{alias}_inverse (x : {ty}) : {other}{alias} ({d}{alias} x) = x := by\n cases x <;> simp [{d}{alias},{other}{alias}]\n#print axioms {d}{alias}_inverse\n'
  t+=f'end NMT_345{label}\n';(E/(mod+'.lean')).write_text(t)
  plans.append(dict(module=mod,kind=kind,type=n,alias=alias,target=cname(n),purpose={'Dec':'CLOSED decoder/validator/encoder exact carriers','Prep':'CLOSED semantic_public exact source carriers','First':'OPEN328 own-argument transport','FIq':'Concrete NKR publicDom caller-clause model'}[label]));prior=mod
(E/'NMT_345_TRANSPORTS.json').write_text(json.dumps(plans,indent=1)+'\n')
(E/'NMT_345TransportBase.lean').write_text('''import NMT_345Context
import NMT_Transport_T16
set_option autoImplicit false
/- Reuse the already checked generic array-map inverse, no duplicate proof. -/
''')
