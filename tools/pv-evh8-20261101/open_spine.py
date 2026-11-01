"""Source-directed per-callee Prefix spines. No opaque helper earns event credit.
All non-language calls are typed, named OPEN obligations, preserving original
parameter lists (including trait dictionaries and callbacks) without evaluating
source Results first. Fail-closed parser; emitted source is never edited.
"""
from pathlib import Path
import ast,re,json,hashlib,subprocess,sys
E=Path('evidence/pv-evh8-20261101')
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
ext=subprocess.check_output(['git','show',rev+':'+p.replace('Funs.lean','ExternalFuns.lean')],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
config={
 'NonzeroStep':'aspis_prover.state_only_entropy.entropy_nonzero32_loop.body',
 'FinishOpening':'prover.finish_opening',
 'PublishCompact':'prover.publish_compact',
 'PrepareOpening':'prover.prepare_opening',
 'SyncDirectory':'aspis_prover.state_only_entropy.sync_directory',
 'NonceReserveFallible':'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible',
 'NonceReserve':'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve',
 'EntropyStep':'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body',
 'NoncePath':'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path',
 'MaterialFromEntropy':'aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref',
 'ApplyMaterial':'aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1',
 'BuildSemantics':'host_semantic.build_with_material',
 'ProveSemantics':'prover.prove_from_semantics',
 'PrivateSalts':'prover.derive_private_salts',
 'MaskedWithAttempt':'prover.prove_masked_with_attempt',
 'DurableWithAttempt':'prover.prove_masked_with_attempt',
 'DurableReserveBuild':'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1',
 'ReserveBuild':'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1'}
short=sys.argv[1];name=config[short];namespace='PV_EVH_'+short
header,result,body,args,explicit=g['get'](name);node=g['parse'](g['normalize'](body))
durable=short in ['DurableReserveBuild','DurableWithAttempt']
joined=short=='DurableWithAttempt'
entropy=short=='EntropyStep'
filemode=short in ['SyncDirectory','NonceReserveFallible','NonceReserve']
primitives={'std.fs.File.open':('openFile','open_fixed fileAnswers _ _ (fun w => files_same.openFile _ _ w)'), 'std.fs.File.sync_all':('sync','sync_fixed fileAnswers _ (fun w => files_same.sync w _)'), 'std.fs.OpenOptions.open':('optionsOpen','options_fixed fileAnswers _ _ _ (fun w => files_same.options _ _ _ w)'), 'std.fs.File.Insts.StdIoWrite.write_all':('writeAll','write_fixed fileAnswers _ _ (fun w => files_same.write w _ _)')}
subcalls={}
valuecalls={}
if short=='PublishCompact':valuecalls={'alloc.vec.Vec.with_capacity':('withCapacity_OPEN','(T : Type) (capacity : Usize)','alloc.vec.Vec T',['T','capacity'])}
if short=='NonceReserveFallible':subcalls={'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path':('PV_EVH_NoncePath','pathCallees'), 'aspis_prover.state_only_entropy.sync_directory':('PV_EVH_SyncDirectory','')}
if short=='NonceReserve':subcalls={'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible':('PV_EVH_NonceReserveFallible','fallibleCallees pathCallees')}
extra_params=''
extra_views=''
if short=='NonceReserveFallible':
 extra_params=' (pathCallees : PV_EVH_NoncePath.Callees)'
 extra_views=' (path_same : PV_EVH_NoncePath.Compatible pathCallees)'
if short=='NonceReserve':
 extra_params=' (fallibleCallees : PV_EVH_NonceReserveFallible.Callees) (pathCallees : PV_EVH_NoncePath.Callees)'
 extra_views=' (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees) (path_same : PV_EVH_NoncePath.Compatible pathCallees)'

store='aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore'
inst=store+'.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore'
reserveLabel=('aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1' if joined else 'state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»')
if durable:
 header=header[header.index('(public1 :' if joined else '(self :'):].replace('(nonce_store : T0)','(nonce_store : '+store+')')
 result=result.replace('× T0','× '+store)
 explicit=explicit[1:]

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
 if label=='alloc.slice.Slice.to_vec':
  return '{T : Type} (inst : core.clone.Clone T) (s : Slice T)','alloc.vec.Vec T',['inst','s'],'toVec_OPEN'
 if label=='alloc.vec.Vec.extend_from_slice':
  return '{T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T)','alloc.vec.Vec T',['inst','v','s'],'extendFromSlice_OPEN'
 if label=='massert':
  return '(condition : Prop) [Decidable condition]','Unit',['condition'],'assert_OPEN'
 if label=='core.option.Option.unwrap':
  return '{T : Type} (value : Option T)','T',['value'],'unwrap_OPEN'
 if label=='core.array.Array.index':
  return '{T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output) (a : Array T N) (i : I)','Output',['inst','a','i'],'arrayIndex_OPEN'
 if label=='core.slice.Slice.copy_from_slice':
  return '{T : Type} (inst : core.marker.Copy T) (dst src : Slice T)','Slice T',['inst','dst','src'],'sliceCopy_OPEN'
 if label=='core.convert.IntoFrom.into':
  return '{T U : Type} (inst : core.convert.From U T) (value : T)','U',['inst','value'],'into_OPEN'
 if label=='core.cmp.PartialEq.ne.trait_default':
  return '{T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U)','Bool',['inst','a','b'],'traitNe_OPEN'
 if label=='core.cmp.impls.PartialEqShared.ne':
  return '{T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U)','Bool',['inst','a','b'],'sharedNe_OPEN'
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
  m=re.search(r'\ndef\s+'+re.escape(label)+r'\s*:\s*Result\s+([\s\S]*?)\s*:=',s);assert m,label
  h,r,ex='',m[1].strip(),[]
  assert '\ndef ' not in r and ':=' not in r,label
 field=label.split('.')[-1]+'_OPEN'
 return h,r,ex,field
spec={label:signature(label) for label in calls if not pure(label) and not (durable and label==reserveLabel) and not (entropy and label=='getrandom.fill') and not (filemode and (label in primitives or label in subcalls))}
fields=[x[3] for x in spec.values()];assert len(set(fields))==len(fields),fields
out=('import PV_EVH_ValueBind\n' if valuecalls else '')+('import PV_EVH_NonceWorld\n'+''.join('import '+m+'\n' for m,_ in subcalls.values()) if filemode else '')+('import PV_EVH_Entropy\nimport PV_EVH_SliceBind\n' if entropy else '')+('import PV_EVH_DurableReserveBuild\n' if joined else 'import PV_EVH_NonceSource\n' if durable else '')+'''import PV_EVH_Prefix
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
for label,(field,h,r,ex) in valuecalls.items():out+='  '+field+' : ∀ '+h+', P ('+r+')\n'
out+='\nstructure Compatible (c : Callees) : Prop where\n'
for label,(h,r,ex,field) in spec.items():
 app=' '.join(ex)
 out+='  '+field.replace('_OPEN','_fixed')+' : '+('∀ '+h+', ' if h else '')+'FinishedView (c.'+field+(' '+app if app else '')+') ('+label+(' '+' '.join(ex[1:]) if label in ['hash','state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»'] else (' '+app if app else ''))+')\n'

for label,(field,h,r,ex) in valuecalls.items():out+='  '+field.replace('_OPEN','_fixed')+' : ∀ '+h+', FinishedView (c.'+field+' '+' '.join(ex)+') (Result.ok ('+label+' '+' '.join(ex)+'))\n'

def valuelet(x):
 if x.kind!='let':return None
 m=re.match(r'let (\w+) := ([\s\S]*)',x.text.strip())
 if not m:return None
 rhs=m[2].strip();label=rhs.split()[0]
 return (m[1],label,rhs[len(label):].strip()) if label in valuecalls else None

def emit(x,n=2,world=False):
 pad=' '*n
 if x.kind=='let' and world and valuelet(x):
  v,label,args=valuelet(x)
  return pad+'let '+v+' ← c.'+valuecalls[label][0]+' '+args+'\n'+emit(x.next,n,world)
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n,world)
 if x.kind=='bind':
  expr=emit(x.expr,n+2,world).lstrip()
  return pad+'let '+x.var+' ← '+expr+'\n'+emit(x.next,n,world)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2,world)+'\n'+pad+'else\n'+emit(x.no,n+2,world)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2,world) for pat,child in x.branches)
 if x.kind=='pure':return pad+('pure ' if world else 'Result.ok ')+x.expr.replace('\n','\n'+pad+'  ')
 exp=x.expr;label=exp.split()[0]
 if joined:exp=exp.replace('aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst',inst)
 if not world:return pad+exp.replace('\n','\n'+pad+'  ')
 if filemode and label in primitives:
  return pad+'PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.'+primitives[label][0]+' fileAnswers '+exp[len(label):].strip().replace('\n',' ')+')'
 if filemode and label in subcalls:
  m,params=subcalls[label]
  args=exp[len(label):].strip().replace('\n',' ')
  tail=(' fileAnswers'+(' '+params if params else '')+' c' if m!='PV_EVH_NoncePath' else ' '+params)
  if m=='PV_EVH_SyncDirectory':tail=' fileAnswers {}'
  if m=='PV_EVH_NonceReserveFallible':tail=' fileAnswers pathCallees fallibleCallees'
  return pad+m+'.run '+args+tail
 if entropy and label=='getrandom.fill':
  return pad+'PV_EVH_Prefix.ofM (PV_EVH_Entropy.draw entropyAnswers '+exp[len(label):].strip()+')'
 if joined and label==reserveLabel:
  args=exp[len(label):].strip().split(None,1)
  assert args[0]==inst
  return pad+'PV_EVH_DurableReserveBuild.run '+args[1].replace('\n',' ')+' fileAnswers reserveCallees'
 if durable and label==reserveLabel:
  return pad+'PV_EVH_Prefix.ofM (PV_EVH_NonceSource.reserve fileAnswers '+exp[len(label):].strip().replace('\n',' ') +')'
 if label in spec:return pad+('c.'+spec[label][3]+(' hash' if label=='hash' else ' state_only_hidingStateOnlyMaskNonceStoreInst' if label=='state_only_hidingStateOnlyMaskNonceStoreInst.«reserve»' else '')+exp[len(label):]).replace('\n','\n'+pad+'  ')
 return pad+'PV_EVH_Prefix.lift ('+exp.replace('\n','\n'+pad+'  ')+')'

def proof(x,n=2,lets=()):
 pad=' '*n
 if x.kind=='let' and valuelet(x):
  v,label,args=valuelet(x)
  return pad+'apply PV_EVH_ValueBind.value_bind_fixed _ ('+label+' '+args+')\n'+pad+'· exact compatible.'+valuecalls[label][0].replace('_OPEN','_fixed')+' '+' '.join('_' for _ in valuecalls[label][3])+'\n'+pad+'·\n'+proof(x.next,n+2,lets)
 if x.kind=='let':
  m=re.match(r'let (\w+) :=',x.text.strip())
  nextlets=lets+((m[1],) if m else ())
  return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+pad+'try dsimp only\n'+proof(x.next,n,nextlets)
 if filemode and x.kind=='bind' and x.expr.kind=='if' and x.expr.yes.kind==x.expr.no.kind==x.next.kind=='pure':
  return pad+'by_cases condition : '+x.expr.cond+'\n'+pad+'· simp only [condition,if_true]\n'+pad+'  exact PV_EVH_Prefix.lift_fixed _\n'+pad+'· simp only [condition,Bool.false_eq_true,if_false]\n'+pad+'  exact PV_EVH_Prefix.lift_fixed _'
 if x.kind=='bind':
  v=x.var;intro='rintro ⟨'+v[1:-1]+'⟩' if v.startswith('(') else 'intro '+v
  if entropy and x.expr.kind=='call' and 'Array.to_slice_mut' in x.expr.expr:
   pureexpr=x.expr.expr.removeprefix('Aeneas.Std.lift (')[:-1]
   names=v[1:-1].split(', ');assert len(names)==2
   return pad+'apply PV_EVH_SliceBind.pure_bind_fixed\n'+pad+'let '+names[0]+' := ('+pureexpr+').1\n'+pad+'let '+names[1]+' := ('+pureexpr+').2\n'+proof(x.next,n,lets+tuple(names))
  return pad+'try dsimp only\n'+pad+'apply PV_EVH_Prefix.bind_fixed\n'+pad+'·\n'+proof(x.expr,n+2,lets)+'\n'+pad+'· '+intro+'\n'+proof(x.next,n+2,lets)
 if x.kind=='if':
  normalize=('try dsimp only ['+','.join(lets)+'] at condition\n'+pad+'  ') if lets else ''
  return pad+'by_cases condition : '+x.cond+'\n'+pad+'· '+normalize+'simp only [condition,if_true]\n'+proof(x.yes,n+2,lets)+'\n'+pad+'· '+normalize+'simp only [condition,if_false]\n'+proof(x.no,n+2,lets)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pat,c) in enumerate(x.branches):
   bits=pat.split();vs=[('unused'+str(j)) if z=='_' else z for z in bits[1:]]
   out+=pad+'| '+bits[0].split('.')[-1]+(' '+' '.join(vs) if vs else '')+' =>\n'+proof(c,n+2,lets)+'\n'
  return out.rstrip()
 if x.kind=='call' and filemode and x.expr.split()[0] in primitives:
  return pad+'exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.'+primitives[x.expr.split()[0]][1]+')'
 if x.kind=='call' and filemode and x.expr.split()[0] in subcalls:
  m,params=subcalls[x.expr.split()[0]]
  if m=='PV_EVH_NoncePath':return pad+'exact PV_EVH_NoncePath.run_fixed _ _ pathCallees path_same'
  if m=='PV_EVH_SyncDirectory':return pad+'exact PV_EVH_SyncDirectory.run_fixed _ fileAnswers {} {} files_same'
  return pad+'exact PV_EVH_NonceReserveFallible.run_fixed _ _ _ fileAnswers pathCallees fallibleCallees fallible_same files_same path_same'
 if x.kind=='call' and entropy and x.expr.split()[0]=='getrandom.fill':
  return pad+'exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_Entropy.draw_fixed entropyAnswers entropy_same _) '
 if x.kind=='call' and joined and x.expr.split()[0]==reserveLabel:
  return pad+'exact PV_EVH_DurableReserveBuild.run_fixed _ _ _ _ _ fileAnswers reserveCallees reserve_same files_same'
 if x.kind=='call' and durable and x.expr.split()[0]==reserveLabel:
  return pad+'exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceSource.reserve_fixed fileAnswers files_same _ _ _)'
 if x.kind=='call' and x.expr.split()[0] in spec:
  h,r,ex,field=spec[x.expr.split()[0]]
  return pad+'exact compatible.'+field.replace('_OPEN','_fixed')+(' '+' '.join(['_']*len(ex)) if ex else '')
 return pad+'exact PV_EVH_Prefix.lift_fixed _'

if entropy or short=='NonzeroStep':out+='\nopen ControlFlow\n'
out+='\ndef run\n  '+header+(' (entropyAnswers : PV_EVH_Entropy.EntropyAnswers)' if entropy else '')+(' (fileAnswers : PV_EVH_NonceWorld.Answers)'+(' (reserveCallees : PV_EVH_DurableReserveBuild.Callees)' if joined else '') if durable or filemode else '')+extra_params+' (c : Callees) : P '+result+' := do\n'+emit(node,world=True)+'\n'
out+='\ntheorem run_fixed\n  '+header+(' (entropyAnswers : PV_EVH_Entropy.EntropyAnswers)' if entropy else '')+(' (fileAnswers : PV_EVH_NonceWorld.Answers)'+(' (reserveCallees : PV_EVH_DurableReserveBuild.Callees)' if joined else '') if durable or filemode else '')+extra_params+' (c : Callees) (compatible : Compatible c)'+(' (entropy_same : ∀ n s, entropyAnswers n s = getrandom.fill s)' if entropy else '')+(' (files_same : PV_EVH_NonceWorld.Compatible fileAnswers)'+(' (reserve_same : PV_EVH_DurableReserveBuild.Compatible reserveCallees)' if joined else '') if durable or filemode else '')+extra_views+' :\n    FinishedView (run '+' '.join(explicit)+(' entropyAnswers' if entropy else '')+(' fileAnswers'+(' reserveCallees' if joined else '') if durable or filemode else '')+(' pathCallees' if short=='NonceReserveFallible' else ' fallibleCallees pathCallees' if short=='NonceReserve' else '')+' c) ('+name+' '+(inst+' ' if durable else '')+' '.join(explicit)+''') := by
  unfold run '''+name+'\n'+proof(node)+'\n\n#print axioms run_fixed\nend '+namespace+'\n'

if entropy or short in ['BuildSemantics','PrepareOpening','NonzeroStep']:out=out.replace('simp only [condition,if_false]', 'simp only [condition,Bool.false_eq_true,if_false]')
if short=='ProveSemantics':out=out.replace(':= by\n  unfold run', ':= by\n  rcases salts with ⟨reserved,context⟩\n  let salts := (reserved,context)\n  unfold run')
if short=='NoncePath' or filemode:out=out.replace('P (','PV_EVH_Prefix.P (')
record=json.dumps(dict(source=p,revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),external_sha256=hashlib.sha256(ext.encode()).hexdigest(),function=name,body_sha256=hashlib.sha256(body.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),open_callees={k:dict(header=v[0],result=v[1],args=v[2],field=v[3]) for k,v in spec.items()},lifted_calls=[c for c in calls if pure(c)],value_callees=valuecalls,scope='source spine only; all named callees and runtime adequacy OPEN'),indent=2)+'\n'
target=Path('lean/'+namespace+'.lean');receipt=E/(short+'-generation.json')
if '--check' in sys.argv:
 assert target.read_text()==out
 assert receipt.read_text()==record
 print('PASS source spine byte identity',short)
else:
 target.write_text(out);receipt.write_text(record)
 print('Generated',short,len(spec),'OPEN callees')
