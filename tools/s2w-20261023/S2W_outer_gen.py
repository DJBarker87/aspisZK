"""Mechanical outer caller monadic port. Helper bodies remain explicit pure Result calls."""
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'AdapterRwModel.lean').read_text();schema=(L/'S2W_Trace.lean').read_text()
block=s.split('structure Ops where\n',1)[1].split('\n\n/--',1)[0]
# Only the final, top-level return changes; Result-valued callbacks remain Result.
fields=re.findall(r'  (op\d+) : (.*?)(?=\n  op\d+ :|\Z)',block,re.S)
ported=[]
for name,typ in fields:
 typ=" ".join(typ.split())
 # Final Result occurs after all callback parentheses have closed.
 depth=0;idx=[]
 for i,c in enumerate(typ):
  if c in '({[':depth+=1
  if c in ')}]':depth-=1
  if depth==0 and typ.startswith('Result ',i):idx.append(i)
 assert len(idx)==1,(name,idx)
 i=idx[0];ported.append('  '+name+' : '+typ[:i]+'M '+typ[i+7:])
header='''import S2W_Trace
/-! Exact monadic port of the two outer caller bodies. Pure helpers are
atomic Result lifts here. This is not an all-helper/native trace claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_Outer
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace
structure Effects (M : Type → Type) where
'''
constructors=schema.split('inductive Call : Type → Type 1 where\n')[1].split('\ndef invoke',1)[0]
source=['def sourceEffects (ops : Ops) : Effects Result := {']
traced=['def traceEffects : Effects Code := {']
# Code is Type→Type1, so Effects must be universe polymorphic.
for name,typ in fields:
 source.append(f'  {name} := ops.{name}')
 line=next(l.strip() for l in constructors.splitlines() if l.strip().startswith('| '+name+' '))
 binders=line.split(' : Call ',1)[0].split(name,1)[1].strip()
 names=re.findall(r'[({]([A-Za-z_][A-Za-z_0-9]*)\s*:',binders)
 # binder types themselves have parentheses: only collect depth-zero binders.
 depth=0;ns=[]
 for i,c in enumerate(binders):
  if c in '({[':
   if depth==0:
    m=re.match(r'[({]([A-Za-z_][A-Za-z_0-9]*)\s*:',binders[i:]);assert m,(name,binders[i:]);ns.append((c,m[1]))
   depth+=1
  if c in ')}]':depth-=1
 pattern=' '.join('{'+n+'}' if c=='{' else n for c,n in ns)
 values=' '.join('('+n+' := '+n+')' if c=='{' else n for c,n in ns)
 traced.append(f'  {name} := '+(f'fun {pattern} => ' if ns else '')+f'perform (. {name} {values})'.replace('. ','.'))
source.append('}\n');traced.append('}\n')
pieces=[]
for short in ['first_decoded','stage1_owned','stage2_owned']:
 old='first_decoded' if short=='first_decoded' else 'r1_pool_adapter.owned.'+short;start=s.index('def '+old+' (ops : Ops)');end=s.find('\n/--',start)
 if end<0:end=s.index('\nend AdapterRw',start)
 body=s[start:end].strip();body=body.replace('def '+old+' (ops : Ops)',f'def {short} {{M : Type → Type}} [Monad M] [MonadLiftT Result M]\n  (ops : Ops) (effects : Effects M)')
 body=re.sub(r'\n  Result ', '\n  M ',body,count=1)
 body=re.sub(r'\bok\b','pure',body)
 # Error converter callbacks are kept Result-valued, not silently coerced.
 body=re.sub(r'ops\.(op\d+)\b',r'effects.\1',body)
 body=body.replace('(effects.op44)','(ops.op44)')
 if short == 'first_decoded':
  body=body.replace('core.result.Result.map_err (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error\n    solana_program_error.ProgramError) r (ops.op44)', 'mapError effects.op44 r')
 else:
  body=body.replace('(first_decoded ops)', '(first_decoded ops effects)')
  body=body.replace('core.result.Result.map_err (BuiltinFnOnce\n                        aspis_r1_cost_probe.verifier.Error\n                        solana_program_error.ProgramError) r6 (ops.op44)', 'mapError effects.op44 r6')
 pieces.append(body)
out=header+'\n'.join(ported)+'\n\n'+'\n'.join(source+traced)+ '''
def mapError {M : Type → Type v} [Monad M] {A E F : Type}
    (f : E → M F) : core.result.Result A E → M (core.result.Result A F)
  | .Ok a => pure (.Ok a)
  | .Err e => do let out ← f e; pure (.Err out)

'''+ '\n\n'.join(pieces)+'''

theorem stage1_source (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    stage1_owned ops (sourceEffects ops) program_id accounts data =
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops program_id accounts data := by rfl

theorem stage2_source (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
    (slot : core.result.Result U64 solana_program_error.ProgramError) :
    stage2_owned ops (sourceEffects ops) program_id accounts data slot =
      r1_pool_adapter.owned.stage2_owned ops program_id accounts data slot := by rfl

#print axioms stage1_source
#print axioms stage2_source
end AspisR1.S2W_Outer
'''
out=out.replace('structure Effects (M : Type → Type)','universe v\nstructure Effects (M : Type → Type v)').replace('{M : Type → Type}', '{M : Type → Type v}')
p=L/'S2W_Outer.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(R/'evidence/s2w-20261023/outer-generation.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'output_sha256':hashlib.sha256(out.encode()).hexdigest(),'scope':'Exact outer two caller bodies with pure helpers still atomic Result lifts; source reconstruction only, not full native observations','transformations':['Top return Result to generic M','ok to pure','direct Ops projections to Effects projections; op44 handled by monadic mapError','first_decoded body ported; other helpers remain atomic Result lifts']},indent=2)+'\n')
