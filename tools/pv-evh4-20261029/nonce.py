"""Selected emitted file-call spines. Other helper effects stay explicit gaps."""
from pathlib import Path
import ast,re,json,hashlib,subprocess
E=Path('evidence/pv-evh4-20261029')
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+p],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text())
g=dict(s=s,re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
base='aspis_prover.state_only_entropy.'
config=[(base+'sync_directory','syncDirectory'),(base+'DurableStateOnlyMaskNonceStore.reserve_fallible','reserveFallible'),(base+'DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve','reserve')]
replacements={old:short+' a' for old,short in config}
primitive={'std.fs.File.open':'openFile a','std.fs.File.sync_all':'sync a','std.fs.OpenOptions.open':'optionsOpen a','std.fs.File.Insts.StdIoWrite.write_all':'writeAll a'}
records=[]
def emit(x,n=2,source=False):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+emit(x.next,n,source)
 if x.kind=='bind':
  structured=x.expr.kind not in ['call','pure']
  return pad+'let '+x.var+' ← '+('do\n'+emit(x.expr,n+2,source) if structured else emit(x.expr,n+2,source).lstrip())+'\n'+emit(x.next,n,source)
 if x.kind=='if':return pad+'if '+x.cond+' then\n'+emit(x.yes,n+2,source)+'\n'+pad+'else\n'+emit(x.no,n+2,source)
 if x.kind=='match':return pad+'match '+x.discr+' with\n'+'\n'.join(pad+'| '+pat+' =>\n'+emit(child,n+2,source) for pat,child in x.branches)
 if x.kind=='pure':return pad+('Result.ok ' if source else 'pure ')+x.expr.replace('\n','\n'+pad+'  ')
 exp=x.expr;label=exp.split()[0]
 if source:return pad+exp.replace('\n','\n'+pad+'  ')
 if label in replacements:return pad+exp.replace(label,replacements[label],1).replace('\n','\n'+pad+'  ')
 if label in primitive:return pad+exp.replace(label,primitive[label],1).replace('\n','\n'+pad+'  ')
 return pad+'PV_EVH_World.lift ('+exp.replace('\n','\n'+pad+'  ')+')'

def proof(x,result,n=2):
 pad=' '*n
 if x.kind=='let':return '\n'.join(pad+z.strip() for z in x.text.splitlines())+'\n'+pad+'try dsimp only\n'+proof(x.next,result,n)
 if x.kind=='bind' and x.expr.kind=='if':
  assert x.expr.yes.kind==x.expr.no.kind==x.next.kind=='pure', 'unsupported effectful structured bind'
  return pad+'by_cases condition : '+x.expr.cond+'\n'+pad+'· simp only [condition,if_true]\n'+pad+'  intro w; rfl\n'+pad+'· simp only [condition,if_false]\n'+pad+'  intro w; rfl'
 if x.kind=='bind':
  var=x.var;intro='rintro ⟨'+var[1:-1]+'⟩' if var.startswith('(') else 'intro '+var
  step='apply fixed_bind'
  if x.expr.kind not in ['call','pure'] or (x.expr.kind=='call' and x.expr.expr.split()[0]=='Aeneas.Std.lift'):
   step+=' (r := (do\n'+emit(x.expr,n+2,True)+')) (f := fun '+var+' => (show Result '+result+' from do\n'+emit(x.next,n+2,True)+'))'
  return pad+'try dsimp only\n'+pad+step+'\n'+pad+'·\n'+proof(x.expr,result,n+2)+'\n'+pad+'· '+intro+'\n'+proof(x.next,result,n+2)
 if x.kind=='if':return pad+'by_cases condition : '+x.cond+'\n'+pad+'· simp only [condition,if_true]\n'+proof(x.yes,result,n+2)+'\n'+pad+'· simp only [condition,if_false]\n'+proof(x.no,result,n+2)
 if x.kind=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+x.discr+' with\n'
  for j,(pat,c) in enumerate(x.branches):
   bits=pat.split();args=[('unused'+str(j)) if z=='_' else z for z in bits[1:]]
   out+=pad+'| '+bits[0].split('.')[-1]+(' '+' '.join(args) if args else '')+' =>\n'+proof(c,result,n+2)+'\n'
  return out.rstrip()
 if x.kind=='pure':return pad+'exact fixed_lift _'
 label=x.expr.split()[0]
 if label in replacements:return pad+'apply '+replacements[label].split()[0]+'_fixed a h'
 laws={'std.fs.File.open':'open_fixed a _ _ (fun w => h.openFile _ _ w)','std.fs.File.sync_all':'sync_fixed a _ (fun w => h.sync w _)','std.fs.OpenOptions.open':'options_fixed a _ _ _ (fun w => h.options _ _ _ w)','std.fs.File.Insts.StdIoWrite.write_all':'write_fixed a _ _ (fun w => h.write w _ _)'}
 return pad+'exact '+laws.get(label,'fixed_lift _')

out='''import PV_EVH_NonceWorld
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonceSource
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_NonceWorld
variable [ExternalTypes] [ExternalFuns]
/- Selected file-call spines only. reservation_path and the other lifted
helpers remain Result-only: allocation/hash/drop source adequacy is OPEN. -/
'''
for old,short in config:
 header,result,body,args,explicit=g['get'](old);node=g['parse'](g['normalize'](body))
 out+='\ndef '+short+' (a : Answers)\n  '+header+' : M '+result+' := do\n'+emit(node)+'\n\n'
 out+='theorem '+short+'_fixed (a : Answers) (h : Compatible a)\n  '+header+' :\n    FixedView ('+short+' a '+' '.join(explicit)+') ('+old+' '+' '.join(explicit)+') := by\n  unfold '+short+' '+old+'\n'+proof(node,result)+'\n\n#print axioms '+short+'_fixed\n'
 records.append(dict(function=old,module_function=short,body_sha256=hashlib.sha256(body.encode()).hexdigest(),body=body))
out+='end PV_EVH_NonceSource\n'
Path('lean/PV_EVH_NonceSource.lean').write_text(out)
(E/'nonce-generation.json').write_text(json.dumps(dict(source=p,source_sha256=hashlib.sha256(s.encode()).hexdigest(),functions=records,scope='selected file-call spine; all other helper effects remain open'),indent=2)+'\n')
