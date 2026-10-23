"""Reify the exact 54 external operation signatures, including higher-order arguments."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'AdapterRwModel.lean').read_text(); block=s.split('structure Ops where\n',1)[1].split('\n\n/--',1)[0]
fields=re.findall(r'  (op\d+) : (.*?)(?=\n  op\d+ :|\Z)',block,re.S);assert len(fields)==54
# Split only arrows and binder separator commas at depth zero.
def split_top(s,sep):
 depth=0;out=[];last=0
 for i,c in enumerate(s):
  if c in '({[':depth+=1
  if c in ')}]':depth-=1
  if depth==0 and s.startswith(sep,i):out.append(s[last:i].strip());last=i+len(sep)
 out.append(s[last:].strip());return out
constructors=[];evals=[];ids=[];dictfields=[];dictvalues=[]
for n,typ in fields:
 typ=' '.join(typ.split());binders='';args=[];tyargs=[]
 if typ.startswith('∀ '):
  prefix,typ=split_top(typ[2:],',');binders=prefix+' '
  # All leading forall binders have explicit names in the source.
  for bracket,name in re.findall(r'([({])([A-Za-z_][A-Za-z_0-9]*)\s*:',prefix):
   tyargs.append(('('+name+' := '+name+')') if bracket=='{' else name)
 parts=split_top(typ,'→');ret=parts.pop();assert ret.startswith('Result '),(n,ret)
 for i,t in enumerate(parts):binders+=f'(a{i} : {t}) ';args.append(f'a{i}')
 result=ret[len('Result '):];constructors.append(f'  | {n} {binders}: Call {result}')
 pattern=' '.join(['.'+n]+(['_']*len(tyargs))+args) # implicit parameters excluded in pattern below
 pattern=' '.join(['@Call.'+n]+[name for _,name in re.findall(r'([({])([A-Za-z_][A-Za-z_0-9]*)\s*:',prefix)]+args) if tyargs else ' '.join(['.'+n]+args)
 evals.append(f'  | {pattern} => ops.{n} '+ ' '.join(tyargs+args))
 ids.append(f'  | {pattern} => {n[2:]}')
 dictfields.append('  '+n+' : '+('∀ '+binders.split(' (a0',1)[0]+', ' if False else ''))
 dictvalues.append(f'  {n} := fun '+ ' '.join(tyargs+args)+' => sorry')
header='''import AdapterRwModel
/-! Typed operation syntax for the adopted dictionary. No argument is serialized,
hashed or replaced by an identifier: Call retains the original typed values.
Only successful external returns append; inner Rust Err is an ordinary value. -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace AspisR1.S2W_Trace
open Aeneas Aeneas.Std Result AdapterRw
universe u v
inductive Call : Type → Type 1 where
'''
out=header+'\n'.join(constructors)+'''\n\ndef invoke (ops : AdapterRw.Ops) {A : Type} : Call A → Result A
'''+ '\n'.join(evals)+'''\n\ndef operationId {A : Type} : Call A → Nat
'''+ '\n'.join(ids)+'''

inductive Event : Type 1 where
  | returned {A : Type} : Call A → A → Event
abbrev Log := List Event
inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step {B : Type} : Result B → (B → Code A) → Code A
  | call {B : Type} : Call B → (B → Code A) → Code A

def bind {A B : Type} : Code A → (A → Code B) → Code B
  | .done a, k => k a
  | .step r c, k => .step r (fun b => bind (c b) k)
  | .call op c, k => .call op (fun b => bind (c b) k)
instance : Monad Code where
  pure := Code.done
  bind := bind

def liftResult {A : Type} (r : Result A) : Code A := .step r .done
instance : MonadLift Result Code where
  monadLift := liftResult

def perform {A : Type} (op : Call A) : Code A := .call op .done

def erase (ops : AdapterRw.Ops) {A : Type} : Code A → Result A
  | .done a => ok a
  | .step r k => do let b ← r; erase ops (k b)
  | .call op k => do let b ← invoke ops op; erase ops (k b)

def thenResult {A : Type u} {B : Type v} (r : Result A) (k : A → Result B) : Result B :=
  match r with
  | .ok a => k a
  | .fail e => .fail e
  | .div => .div

def forget {A : Type} (r : Result (A × Log)) : Result A :=
  thenResult r (fun x => ok x.1)

def run (ops : AdapterRw.Ops) {A : Type} : Code A → Log → Result (A × Log)
  | .done a, log => ok (a,log)
  | .step r k, log => thenResult r (fun b => run ops (k b) log)
  | .call op k, log => thenResult (invoke ops op) (fun b =>
      run ops (k b) (log ++ [.returned op b]))

theorem erase_run (ops : AdapterRw.Ops) {A : Type} (p : Code A) (log : Log) :
    forget (run ops p log) = erase ops p := by
  induction p generalizing log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok b => exact ih b log
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [run,thenResult,forget,erase,h,bind_tc_fail]
    | div => simp only [run,thenResult,forget,erase,h,bind_tc_div]
    | ok b => simpa only [run,thenResult,erase,h,bind_tc_ok] using ih b (log ++ [.returned op b])

theorem run_prefix (ops : AdapterRw.Ops) {A : Type} (p : Code A)
    (before after : Log) (a : A) (success : run ops p before = ok (a,after)) :
    ∃ suffix, after = before ++ suffix := by
  induction p generalizing before after with
  | done b =>
    have eq := Result.ok.inj success
    exact ⟨[], by simpa using congrArg Prod.snd eq.symm⟩
  | step r k ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok b => exact ih b before after success
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [run,thenResult,h]  at success; cases success
    | div => simp only [run,thenResult,h]  at success; cases success
    | ok b =>
      simp only [run,thenResult,h] at success
      obtain ⟨suffix,hs⟩ := ih b _ after success
      exact ⟨.returned op b :: suffix, by simpa only [List.append_assoc,List.singleton_append] using hs⟩

theorem erase_perform (ops : AdapterRw.Ops) {A : Type} (op : Call A) :
    erase ops (perform op) = invoke ops op := by
  cases h : invoke ops op <;> simp only [perform,erase,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem erase_lift (ops : AdapterRw.Ops) {A : Type} (r : Result A) :
    erase ops (liftResult r) = r := by cases r <;> rfl

theorem erase_bind (ops : AdapterRw.Ops) {A B : Type} (p : Code A) (k : A → Code B) :
    erase ops (p >>= k) = (do let a ← erase ops p; erase ops (k a)) := by
  induction p with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; erase ops (bind (c b) k)) = _
    have h : ∀ b, erase ops (bind (c b) k) =
      (do let a ← erase ops (c b); erase ops (k a)) := ih
    simp only [h,erase]
    cases r <;> rfl
  | call op c ih =>
    change (do let b ← invoke ops op; erase ops (bind (c b) k)) = _
    have h : ∀ b, erase ops (bind (c b) k) =
      (do let a ← erase ops (c b); erase ops (k a)) := ih
    simp only [h,erase]
    cases invoke ops op <;> rfl

#print axioms erase_run
#print axioms run_prefix
#print axioms erase_perform
#print axioms erase_lift
#print axioms erase_bind
end AspisR1.S2W_Trace
'''
p=L/'S2W_Trace.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(R/'evidence/s2w-20261023/trace-generation.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'output_sha256':hashlib.sha256(out.encode()).hexdigest(),'operations':len(fields),'scope':'Typed signature reification and generic interpreter; caller port not claimed'},indent=2)+'\n')
