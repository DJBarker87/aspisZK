"""Exact masked-attempt source spine; every opaque callee stays named OPEN."""
from pathlib import Path
import ast,re,json,hashlib,subprocess,sys
E=Path('evidence/pv-evh5-20261029')
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
header,result,body,args,explicit=g['get']('prover.prove_masked_attempt');node=g['parse'](g['normalize'](body))
# Opaque source operations are not lifted as if effect free.
ops={
 'aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes':('publicBytes_OPEN','public1'),
 'hash':('hash_OPEN',None),
 'aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1':('context_OPEN','a a1'),
 'aspis_core.state_only_hiding.StateOnlyHidingContext.encode':('encode_OPEN','context'),
 'transport.Variant.tag':('tag_OPEN','variant'),
 'prover.prove_masked_with_attempt':('withAttempt_OPEN','context binding attempt nonce_store')}
out='''import PV_EVH_AccountEntry
set_option autoImplicit false
noncomputable section
namespace PV_EVH_MaskedAttempt
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash)
open PV_EVH_RetryBody (Store Secrets AttemptOutcome)
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext

/-- Individual unexpanded source callees, not a whole-attempt answer/trace.
These remain proof work; no native effect coverage is asserted for them. -/
structure Callees where
  publicBytes_OPEN : Public → P (core.result.Result (alloc.vec.Vec U8) aspis_core.state_only_prefix.r0.Error)
  hash_OPEN : Slice (Slice U8) → P (Array U8 32#usize)
  context_OPEN : Array U8 32#usize → Array U8 32#usize → P Context
  encode_OPEN : Context → P (Array U8 81#usize)
  tag_OPEN : transport.Variant → P U8
  withAttempt_OPEN : Context → Array U8 32#usize → Secrets → Store → P AttemptOutcome

structure Compatible (c : Callees) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : Prop where
  publicBytes_fixed : ∀ p, FinishedView (c.publicBytes_OPEN p)
    (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p)
  hash_fixed : ∀ s, FinishedView (c.hash_OPEN s) (hash s)
  context_fixed : ∀ a b, FinishedView (c.context_OPEN a b)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 a b)
  encode_fixed : ∀ a, FinishedView (c.encode_OPEN a)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.encode a)
  tag_fixed : ∀ v, FinishedView (c.tag_OPEN v) (transport.Variant.tag v)
  withAttempt_fixed : ∀ context binding attempt store,
    FinishedView (c.withAttempt_OPEN context binding attempt store)
      (prover.prove_masked_with_attempt
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        public1 compiled variant hash context binding attempt store)
'''
def emit(x,n=2,world=False):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n,world)
 if x.kind=='bind':return pad+'let '+x.var+' ← '+emit(x.expr,n+2,world).lstrip()+'\n'+emit(x.next,n,world)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2,world)+'\n'+pad+'else\n'+emit(x.no,n+2,world)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2,world) for pat,child in x.branches)
 if x.kind=='pure':return pad+('pure ' if world else 'Result.ok ')+x.expr
 exp=x.expr;label=exp.split()[0]
 if not world:return pad+exp.replace('\n','\n'+pad+'  ')
 if label in ops:
  name,arguments=ops[label]
  return pad+'c.'+name+' '+(arguments if arguments is not None else exp[len(label):].strip())
 return pad+'PV_EVH_Prefix.lift ('+exp.replace('\n','\n'+pad+'  ')+')'
def proof(x,n=2):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+pad+'try dsimp only\n'+proof(x.next,n)
 if x.kind=='bind':
  var=x.var;intro='rintro ⟨'+var[1:-1]+'⟩' if var.startswith('(') else 'intro '+var
  return pad+'try dsimp only\n'+pad+'apply PV_EVH_Prefix.bind_fixed\n'+pad+'·\n'+proof(x.expr,n+2)+'\n'+pad+'· '+intro+'\n'+proof(x.next,n+2)
 if x.kind=='if':return pad+'by_cases condition : '+x.cond+'\n'+pad+'· simp only [condition,if_true]\n'+proof(x.yes,n+2)+'\n'+pad+'· simp only [condition,if_false]\n'+proof(x.no,n+2)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pat,c) in enumerate(x.branches):
   bits=pat.split();vs=[('unused'+str(j)) if z=='_' else z for z in bits[1:]]
   out+=pad+'| '+bits[0].split('.')[-1]+(' '+' '.join(vs) if vs else '')+' =>\n'+proof(c,n+2)+'\n'
  return out.rstrip()
 if x.kind=='pure':return pad+'exact PV_EVH_Prefix.lift_fixed _'
 label=x.expr.split()[0]
 if label in ops:
  field=ops[label][0].replace('_OPEN','_fixed')
  arity={'publicBytes_fixed':1,'hash_fixed':1,'context_fixed':2,'encode_fixed':1,'tag_fixed':1,'withAttempt_fixed':4}[field]
  return pad+'exact compatible.'+field+' '+' '.join(['_']*arity)
 return pad+'exact PV_EVH_Prefix.lift_fixed _'
out+='\n/-- Source spine only; all effectful opaque callees above remain OPEN. -/\ndef run\n  '+header+' (c : Callees) : P AttemptOutcome := do\n'+emit(node,world=True)+'\n'
out+='\ntheorem run_fixed\n  '+header+' (c : Callees)\n    (compatible : Compatible c public1 compiled variant hash) :\n    FinishedView (run '+' '.join(explicit)+''' c)
      (prover.prove_masked_attempt '''+' '.join(explicit)+''') := by
  unfold run prover.prove_masked_attempt
'''+proof(node)+'\n\n#print axioms run_fixed\nend PV_EVH_MaskedAttempt\n'
record=json.dumps(dict(source=p,revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),function='prover.prove_masked_attempt',body_sha256=hashlib.sha256(body.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),open_callees=ops,scope='source spine with six explicit unexpanded callees; not complete native world'),indent=2)+'\n'
target=Path('lean/PV_EVH_MaskedAttempt.lean')
if '--check' in sys.argv:
 assert target.read_text()==out
 assert (E/'masked-generation.json').read_text()==record
 print('PASS masked-attempt source generation byte identity')
else:
 target.write_text(out)
 (E/'masked-generation.json').write_text(record)
