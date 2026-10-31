"""Reify the exact extracted retry spine; callee interpretations remain OPEN."""
from pathlib import Path
import ast,re,json,hashlib,subprocess
E=Path('evidence/pv-evh5-20261029')
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show','8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7:'+p],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
header,result,body,args,explicit=g['get']('prover.retry_attempt');node=g['parse'](g['normalize'](body))
# Use the exact Rust/extraction type carriers, avoiding a port or new extraction.
out='''import PV_EVH_WorldLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RetryBody
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Outcome := (core.result.Result prover.RetriedProof verifier.Error) × Store
abbrev AttemptOutcome := (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × Store
abbrev Next (T : Type) := T → Usize → M ((core.result.Result Secrets verifier.Error) × T)
abbrev Prove := Secrets → Store → M AttemptOutcome
abbrev State (T : Type) := Store × T × Usize
'''
header=header.replace('{T0 : Type}','{T0 : Type}')
# Both generated functions have the original binders. World callbacks are explicit.
worldhead=header+' (next_OPEN : Next T0) (prove_OPEN : Prove)'

def emit(x,n=2,world=False):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n,world)
 if x.kind=='bind':
  expr=emit(x.expr,n+2,world).lstrip()
  return pad+'let '+x.var+' ← '+expr+'\n'+emit(x.next,n,world)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2,world)+'\n'+pad+'else\n'+emit(x.no,n+2,world)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2,world) for pat,child in x.branches)
 if x.kind=='pure':return pad+('pure ' if world else 'Result.ok ')+'(ControlFlow.done ('+x.expr+'))'
 exp=x.expr;label=exp.split()[0]
 if label=='prover.retry_attempt':
  call='pure (ControlFlow.cont (nonce_store1, next_attempt1, i))' if world else 'Result.ok (ControlFlow.cont (nonce_store1, next_attempt1, i))'
  return pad+('do\n'+pad+'  let _ ← PV_EVH_World.retry\n'+pad+'  '+call if world else call)
 if not world:return pad+exp.replace('\n','\n'+pad+'  ')
 if label.endswith('.call_mut') and label.startswith('coreopsfunction'):
  return pad+'next_OPEN next_attempt k'
 if label=='prover.prove_masked_attempt':
  return pad+'(do\n'+pad+'  let _ ← PV_EVH_World.attempt\n'+pad+'  prove_OPEN val nonce_store)'
 return pad+'PV_EVH_World.lift ('+exp.replace('\n','\n'+pad+'  ')+')'

out+='\ndef sourceBody\n  '+header+' : Result (ControlFlow (State T0) Outcome) := do\n'+emit(node)+'\n'
out+='\n/-- Only the retry source spine. Both callee interpreters are OPEN. -/\ndef body\n  '+worldhead+' : M (ControlFlow (State T0) Outcome) := do\n'+emit(node,world=True)+'\n'
# Fixed-view proof follows source AST, never unfolds proof arithmetic.
def proof(x,n=2):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+pad+'try dsimp only\n'+proof(x.next,n)
 if x.kind=='bind':
  var=x.var;intro='rintro ⟨'+var[1:-1]+'⟩' if var.startswith('(') else 'intro '+var
  return pad+'try dsimp only\n'+pad+'apply fixed_bind\n'+pad+'·\n'+proof(x.expr,n+2)+'\n'+pad+'· '+intro+'\n'+proof(x.next,n+2)
 if x.kind=='if':return pad+'by_cases condition : '+x.cond+'\n'+pad+'· simp only [condition,if_true]\n'+proof(x.yes,n+2)+'\n'+pad+'· simp only [condition,if_false]\n'+proof(x.no,n+2)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pat,c) in enumerate(x.branches):
   bits=pat.split();args=[('unused'+str(j)) if z=='_' else z for z in bits[1:]]
   out+=pad+'| '+bits[0].split('.')[-1]+(' '+' '.join(args) if args else '')+' =>\n'+proof(c,n+2)+'\n'
  return out.rstrip()
 if x.kind=='pure':return pad+'exact fixed_lift _'
 label=x.expr.split()[0]
 if label=='prover.retry_attempt':return pad+'intro w; rfl'
 if label.endswith('.call_mut') and label.startswith('coreopsfunction'):return pad+'exact next_fixed _ _'
 if label=='prover.prove_masked_attempt':return pad+'intro w\n'+pad+'exact prove_fixed _ _ _'
 return pad+'exact fixed_lift _'
app=' '.join(explicit)
out+='\ntheorem body_fixed\n  '+worldhead+'''
    (next_fixed : ∀ c k, FixedView (next_OPEN c k)
      (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut c k))
    (prove_fixed : ∀ a st, FixedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled variant hash a st)) :
    FixedView (body '''+app+''' next_OPEN prove_OPEN)
      (sourceBody '''+app+''') := by
  unfold body sourceBody
'''+proof(node)+'\n\n#print axioms body_fixed\nend PV_EVH_RetryBody\n'
Path('lean/PV_EVH_RetryBody.lean').write_text(out)
(E/'retry-generation.json').write_text(json.dumps(dict(source=p,revision='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7',source_sha256=hashlib.sha256(s.encode()).hexdigest(),function='prover.retry_attempt',body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),scope='source retry spine only; next_OPEN and prove_OPEN uninstantiated'),indent=2)+'\n')
