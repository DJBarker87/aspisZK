"""Reinterpret ONE existing emitted body; no Rust/extractor/source changes."""
from pathlib import Path
import subprocess,re,hashlib,json
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+p],text=True)
name='aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body'
start=s.index('def\n  '+name);end=s.index('\n/--',start)
body=s[start:end]
assert body.count('getrandom.fill s')==1
body=body.replace('def\n  '+name,'def entropyBody (answers : EntropyAnswers)')
body=body.replace('  Result (ControlFlow','  M (ControlFlow',1).replace('getrandom.fill s','draw answers s')
body=re.sub(r'\bok \(', 'pure (',body)
header='''import PV_EVH_World
set_option autoImplicit false
noncomputable section
namespace PV_EVH_Entropy
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_EVH_World
open PV_RJ4IDB (NativeEvent)
variable [ExternalTypes] [ExternalFuns]

abbrev FillReply := Result ((core.result.Result Unit getrandom.error.Error) × Slice U8)
abbrev EntropyAnswers := Nat → Slice U8 → FillReply

def ascii (s : String) : PV_RJ4IDB.Bytes :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

def draw (answers : EntropyAnswers) (buffer : Slice U8) : M
    ((core.result.Result Unit getrandom.error.Error) × Slice U8) := fun w =>
  let r := answers w.entropyCursor buffer
  let next := {w with entropyCursor := w.entropyCursor + 1}
  let request := NativeEvent.side (ascii "entropy-request") (ascii (toString w.entropyCursor))
  match r with
  | .div => ⟨.div,next,[request]⟩
  | _ => ⟨r,next,[request,
      .side (ascii "entropy-delivery") (ascii (toString w.entropyCursor))]⟩

theorem draw_fixed (answers : EntropyAnswers)
    (h : ∀ n s, answers n s = getrandom.fill s) (buffer : Slice U8) :
    FixedView (draw answers buffer) (getrandom.fill buffer) :=
  by
    intro w
    cases hr : answers w.entropyCursor buffer <;>
      simpa only [draw,hr] using h w.entropyCursor buffer

/- Exact emitted body, only monad lift / entropy primitive interpretation.
Every other helper remains a fixed Result call: whole-prover event credit is
NOT claimed. The structural diff and original hash are recorded separately. -/
'''
footer='''
#print axioms draw_fixed
end PV_EVH_Entropy
'''
Path('lean/PV_EVH_Entropy.lean').write_text(header+body+footer)
Path('evidence/pv-evh4-20261029/entropy-generation.json').write_text(json.dumps(dict(source=p,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(s[start:end].encode()).hexdigest(),changes=['Result return interpreted as M','one getrandom.fill replaced by draw','ok terminals interpreted as pure','other Result actions lifted explicitly'],source_body=s[start:end],status='single-body reinterpretation; other helpers still Result-only'),indent=2)+'\n')
# Reuse only the reviewed syntax parser definitions, without executing another
# job's generator or touching its output/evidence directories.
import ast
parser=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text())
selected=[n for n in parser.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse']]
ns={};exec(compile(ast.Module(body=selected,type_ignores=[]),'<reviewed-parser>','exec'),ns)
node=ns['parse'](ns['normalize'](s[start:end].split(':= do\n',1)[1]))

def emit(x,n=2):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n)
 if x.kind=='bind':return pad+'let '+x.var+' ← '+emit(x.expr,n+2).lstrip()+'\n'+emit(x.next,n)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2)+'\n'+pad+'else\n'+emit(x.no,n+2)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2) for pat,child in x.branches)
 if x.kind=='pure':return pad+'pure '+x.expr.replace('\n','\n'+pad+'  ')
 if x.expr.split()[0]=='getrandom.fill':return pad+x.expr.replace('getrandom.fill','draw answers',1)
 return pad+'PV_EVH_World.lift ('+x.expr.replace('\n','\n'+pad+'  ')+')'
body=body.split(':= do\n',1)[0]+':= do\n'+emit(node)+'\n'
Path('lean/PV_EVH_Entropy.lean').write_text(header+body+footer)

def source_emit(x,n=2):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+source_emit(x.next,n)
 if x.kind=='bind':
  structured=x.expr.kind not in ['call','pure']
  return pad+'let '+x.var+' ← '+('do\n'+source_emit(x.expr,n+2) if structured else source_emit(x.expr,n+2).lstrip())+'\n'+source_emit(x.next,n)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+source_emit(x.yes,n+2)+'\n'+pad+'else\n'+source_emit(x.no,n+2)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+source_emit(child,n+2) for pat,child in x.branches)
 if x.kind=='pure':return pad+'ok '+x.expr.replace('\n','\n'+pad+'  ')
 return pad+x.expr.replace('\n','\n'+pad+'  ')

def proof(x,n=2):
 pad=' '*n
 if x.kind=='let':return pad+'try dsimp only\n'+proof(x.next,n)
 if x.kind=='bind':
  var=x.var;intro='rintro ⟨'+var[1:-1]+'⟩' if var.startswith('(') else 'intro '+var
  return pad+'try dsimp only\n'+pad+'apply fixed_bind (r := (do\n'+source_emit(x.expr,n+2)+')) (f := fun '+var+' => do\n'+source_emit(x.next,n+2)+')\n'+pad+'·\n'+proof(x.expr,n+2)+'\n'+pad+'· '+intro+'\n'+proof(x.next,n+2)
 if x.kind=='if':
  return pad+'by_cases condition : '+x.cond+'\n'+pad+'· simp only [condition,if_true]\n'+proof(x.yes,n+2)+'\n'+pad+'· simp only [condition,if_false]\n'+proof(x.no,n+2)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pattern,child) in enumerate(x.branches):
   bits=pattern.split();ctor=bits[0].split('.')[-1];args=[('unused'+str(j)) if b=='_' else b for b in bits[1:]]
   out+=pad+'| '+ctor+(' '+' '.join(args) if args else '')+' =>\n'+proof(child,n+2)+'\n'
  return out.rstrip()
 if x.kind=='pure':return pad+'exact fixed_lift _'
 return pad+('exact draw_fixed answers h _' if x.expr.split()[0]=='getrandom.fill' else 'exact fixed_lift _')
theorem='''
/-- Complete Result equality for this actual emitted iteration, on the fixed
answer view. This restriction is deliberately not imposed on the world loop. -/
theorem entropyBody_fixed (answers : EntropyAnswers)
    (h : ∀ n s, answers n s = getrandom.fill s)
    (nonce : Array U8 32#usize) (limit retry : Usize) :
    FixedView (entropyBody answers nonce limit retry)
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit retry) := by
  unfold entropyBody aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
'''+proof(node)+'''

#print axioms entropyBody_fixed
'''
p=Path('lean/PV_EVH_Entropy.lean');p.write_text(p.read_text().replace(footer,theorem+footer))
