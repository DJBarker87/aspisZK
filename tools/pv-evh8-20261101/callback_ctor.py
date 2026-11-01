"""Concrete source callback constructors with explicit native drops."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh8-20261101');rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
out='''import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_CallbackCtor
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Constructor callbacks execute native argument/capture drops first. Their
actual drop associations, operator selection and runtime adequacy remain OPEN. -/
'''
rows=[]
for i,v in enumerate(json.load(open(E/'callback-frontier.json'))['callbacks']):
 if 'body' not in v:continue
 name='callback_'+str(i);fn=v['callback'];h,r,b,_,ex=g['get'](fn);m=re.fullmatch(r'\s*ok (\w+(?:\.\w+)*)\s*',b);assert m,b
 value=m[1];args=' '.join(ex)
 cap=re.search(r'\(c : ([\s\S]*?)\)\s*\(tupled_args :',h)[1]
 arg=re.search(r'\(tupled_args : ([\s\S]*?)\)\s*$',h)[1]
 drops=' (dropArgument : '+arg+' → P Unit) (dropCapture : '+cap+' → P Unit)'
 out+='\ndef '+name+' '+h+drops+' : P '+r+' := do\n  let _ ← dropArgument tupled_args\n  let _ ← dropCapture c\n  pure '+value+'\n'
 out+='\ntheorem '+name+'_fixed '+h+drops+'\n    (ha : FinishedView (dropArgument tupled_args) (.ok ()))\n    (hc : FinishedView (dropCapture c) (.ok ())) :\n    FinishedView ('+name+' '+args+' dropArgument dropCapture) ('+fn+' '+args+') := by\n'
 out+='  exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok '+value+') ha\n    (fun _ => PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok '+value+') hc\n      (fun _ => PV_EVH_Prefix.lift_fixed (.ok '+value+')))\n'
 out+='\n#print axioms '+name+'_fixed\n'
 rows.append(dict(name=name,source_callback=fn,body_sha256=hashlib.sha256(b.encode()).hexdigest(),native_status='OPEN capture/argument drop and source/native association'))
out+='end PV_EVH_CallbackCtor\n'
record=json.dumps(dict(status='source callback value laws only',source=p,revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),callbacks=rows,output_sha256=hashlib.sha256(out.encode()).hexdigest()),indent=2)+'\n'
q=Path('lean/PV_EVH_CallbackCtor.lean');receipt=E/'callback-ctor-generation.json'
if '--check' in sys.argv:assert q.read_text()==out and receipt.read_text()==record
else:q.write_text(out);receipt.write_text(record)
print('Callback constructor source laws:',len(rows),'; native drops remain OPEN')
