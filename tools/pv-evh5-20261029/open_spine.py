"""Source-directed per-callee Prefix spines. No opaque helper earns event credit.
All non-language calls are typed, named OPEN obligations, preserving original
parameter lists (including trait dictionaries and callbacks) without evaluating
source Results first. Fail-closed parser; emitted source is never edited.
"""
from pathlib import Path
import ast,re,json,hashlib,subprocess,sys
E=Path('evidence/pv-evh5-20261029')
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
ext=subprocess.check_output(['git','show',rev+':'+p.replace('Funs.lean','ExternalFuns.lean')],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
config={
 'MaskedWithAttempt':'prover.prove_masked_with_attempt',
 'ReserveBuild':'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1'}
short=sys.argv[1];name=config[short];namespace='PV_EVH_'+short
header,result,body,args,explicit=g['get'](name);node=g['parse'](g['normalize'](body))
calls=[]
def walk(x):
 if x.kind=='bind':walk(x.expr);walk(x.next)
 elif x.kind=='let':walk(x.next)
 elif x.kind=='if':walk(x.yes);walk(x.no)
 elif x.kind=='match':
  for _,c in x.branches:walk(c)
 elif x.kind=='call':
  label=x.expr.split()[0]
  if label not in calls:calls.append(label)
walk(node)
# Only language-level Result combinators and checked value/slice primitives are
# lifted. Native panic/abort/drop/allocator adequacy is still unproved.
pure=lambda label:label.startswith('core.result.') or label in ['Aeneas.Std.lift','Array.index_usize']

def binder_names(h):
 pos=0;ex=[]
 while pos<len(h):
  while pos<len(h) and h[pos].isspace():pos+=1
  if pos==len(h):break
  start=pos;assert h[pos] in '({',h[pos:];depth=0
  while pos<len(h):
   ch=h[pos]
   if ch in '({[':depth+=1
   elif ch in ')}]':depth-=1
   pos+=1
   if depth==0:break
  if h[start]=='(':ex+=h[start+1:pos-1].split(':',1)[0].split()
 return ex

def signature(label):
 alias=re.search(r'abbrev '+re.escape(label)+r' .*? := @ExternalFuns\.(op\d+)\b',ext)
 if alias:
  op=alias[1];start=ext.index('\n  '+op)+3;end=ext.find('\n  op',start)
  raw=ext[start:end].strip()[len(op):].strip();depth=0;cut=None
  for i,ch in enumerate(raw):
   if ch in '({[':depth+=1
   elif ch in ')}]':depth-=1
   elif ch==':' and depth==0:cut=i;break
  assert cut is not None,raw
  h=raw[:cut].strip();typ=' '.join(raw[cut+1:].split());parts=[];depth=0;last=0
  for i,ch in enumerate(typ):
   if ch in '({[':depth+=1
   elif ch in ')}]':depth-=1
   elif ch=='→' and depth==0:parts.append(typ[last:i].strip());last=i+1
  parts.append(typ[last:].strip());ret=parts.pop();assert ret.startswith('Result '),ret
  h+=''.join(' (arg'+str(i)+' : '+v+')' for i,v in enumerate(parts))
  return h.strip(),ret[7:].strip(),binder_names(h),op+'_OPEN'
 if label=='core.array.equality.PartialEqArray.ne':
  return '{T : Type} {N : Usize} (inst : core.cmp.PartialEq T T) (a b : Array T N)','Bool',['inst','a','b'],'arrayNe_OPEN'
 if label=='hash':
  return '(hash : Slice (Slice U8) → Result (Array U8 32#usize)) (s : Slice (Slice U8))','(Array U8 32#usize)',['hash','s'],'hash_OPEN'
 if label=='state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»':
  return '{T0 : Type} (state_only_hidingStateOnlyMaskNonceStoreInst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) (store : T0) (digest nonce : Array U8 32#usize)','(Bool × T0)',['state_only_hidingStateOnlyMaskNonceStoreInst','store','digest','nonce'],'reserve_OPEN'
 if label=='alloc.vec.from_elem':
  return '{T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize)','alloc.vec.Vec T',['inst','value','count'],'fromElem_OPEN'
 try:
  h,r,_,_,ex=g['get'](label)
 except AssertionError:
  # Source constants have no argument binder and therefore are not matched by get.
  m=re.search(r'\ndef\s+'+re.escape(label)+r'\s*:\s*Result\s+([\s\S]*?)\n  := do',s);assert m,label
  h,r,ex='',m[1].strip(),[]
 field=label.split('.')[-1]+'_OPEN'
 return h,r,ex,field
spec={label:signature(label) for label in calls if not pure(label)}
fields=[x[3] for x in spec.values()];assert len(set(fields))==len(fields),fields
out='''import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace '''+namespace+'''
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
'''
for label,(h,r,ex,field) in spec.items():out+='  '+field+' : '+('∀ '+h+', ' if h else '')+'P ('+r+')\n'
out+='\nstructure Compatible (c : Callees) : Prop where\n'
for label,(h,r,ex,field) in spec.items():
 app=' '.join(ex)
 out+='  '+field.replace('_OPEN','_fixed')+' : '+('∀ '+h+', ' if h else '')+'FinishedView (c.'+field+(' '+app if app else '')+') ('+label+(' '+' '.join(ex[1:]) if label in ['hash','state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»'] else (' '+app if app else ''))+')\n'

def emit(x,n=2,world=False):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n,world)
 if x.kind=='bind':
  expr=emit(x.expr,n+2,world).lstrip()
  return pad+'let '+x.var+' ← '+expr+'\n'+emit(x.next,n,world)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2,world)+'\n'+pad+'else\n'+emit(x.no,n+2,world)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2,world) for pat,child in x.branches)
 if x.kind=='pure':return pad+('pure ' if world else 'Result.ok ')+x.expr.replace('\n','\n'+pad+'  ')
 exp=x.expr;label=exp.split()[0]
 if not world:return pad+exp.replace('\n','\n'+pad+'  ')
 if label in spec:return pad+('c.'+spec[label][3]+(' hash' if label=='hash' else ' state_only_hidingStateOnlyMaskNonceStoreInst' if label=='state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»' else '')+exp[len(label):]).replace('\n','\n'+pad+'  ')
 return pad+'PV_EVH_Prefix.lift ('+exp.replace('\n','\n'+pad+'  ')+')'

def proof(x,n=2,lets=()):
 pad=' '*n
 if x.kind=='let':
  m=re.match(r'let (\w+) :=',x.text.strip())
  nextlets=lets+((m[1],) if m else ())
  return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+pad+'try dsimp only\n'+proof(x.next,n,nextlets)
 if x.kind=='bind':
  v=x.var;intro='rintro ⟨'+v[1:-1]+'⟩' if v.startswith('(') else 'intro '+v
  return pad+'try dsimp only\n'+pad+'apply PV_EVH_Prefix.bind_fixed\n'+pad+'·\n'+proof(x.expr,n+2,lets)+'\n'+pad+'· '+intro+'\n'+proof(x.next,n+2,lets)
 if x.kind=='if':
  normalize=('dsimp only ['+','.join(lets)+'] at condition\n'+pad+'  ') if lets else ''
  return pad+'by_cases condition : '+x.cond+'\n'+pad+'· '+normalize+'simp only [condition,if_true]\n'+proof(x.yes,n+2,lets)+'\n'+pad+'· '+normalize+'simp only [condition,if_false]\n'+proof(x.no,n+2,lets)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pat,c) in enumerate(x.branches):
   bits=pat.split();vs=[('unused'+str(j)) if z=='_' else z for z in bits[1:]]
   out+=pad+'| '+bits[0].split('.')[-1]+(' '+' '.join(vs) if vs else '')+' =>\n'+proof(c,n+2,lets)+'\n'
  return out.rstrip()
 if x.kind=='call' and x.expr.split()[0] in spec:
  h,r,ex,field=spec[x.expr.split()[0]]
  return pad+'exact compatible.'+field.replace('_OPEN','_fixed')+(' '+' '.join(['_']*len(ex)) if ex else '')
 return pad+'exact PV_EVH_Prefix.lift_fixed _'

out+='\ndef run\n  '+header+' (c : Callees) : P '+result+' := do\n'+emit(node,world=True)+'\n'
out+='\ntheorem run_fixed\n  '+header+' (c : Callees) (compatible : Compatible c) :\n    FinishedView (run '+' '.join(explicit)+' c) ('+name+' '+' '.join(explicit)+''') := by
  unfold run '''+name+'\n'+proof(node)+'\n\n#print axioms run_fixed\nend '+namespace+'\n'
record=json.dumps(dict(source=p,revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),external_sha256=hashlib.sha256(ext.encode()).hexdigest(),function=name,body_sha256=hashlib.sha256(body.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),open_callees={k:dict(header=v[0],result=v[1],args=v[2],field=v[3]) for k,v in spec.items()},lifted_calls=[c for c in calls if pure(c)],scope='source spine only; all named callees and runtime adequacy OPEN'),indent=2)+'\n'
target=Path('lean/'+namespace+'.lean');receipt=E/(short+'-generation.json')
if '--check' in sys.argv:
 assert target.read_text()==out
 assert receipt.read_text()==record
 print('PASS source spine byte identity',short)
else:
 target.write_text(out);receipt.write_text(record)
 print('Generated',short,len(spec),'OPEN callees')
