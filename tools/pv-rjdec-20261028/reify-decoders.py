"""Reify pinned parser bodies using the existing pv-world syntax translator.
No source function is evaluated, rewritten, or treated as a pure native call.
"""
from pathlib import Path
import subprocess,json,re,hashlib,ast
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rjdec-20261028'
plan=json.loads((E/'build-plan.json').read_text());pin=plan['modules']['AspisR1TerminalDecoder.Funs'];b=subprocess.check_output(['git','show','HEAD:'+pin['path']]);assert hashlib.sha256(b).hexdigest()==pin['sha256'];s=b.decode()
old=subprocess.check_output(['git','show','HEAD:tools/pv-world-20261028/reify-recursive.py'],text=True)
nodes=[n for n in ast.parse(old).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))]
ns=dict(re=re,json=json,s=s);exec(compile(ast.Module(body=nodes,type_ignores=[]),'pv-world-pinned-translator','exec'),ns)
# Preserve the emitted RHS column when a then/else/match arm starts inline.
# Later statements of that arm are aligned to that column by Lean's printer.
def normalize_columns(body):
 lines=body.splitlines();out=[];i=0
 while i<len(lines):
  line=lines[i];i+=1
  if not line.strip():continue
  pad=' '*ns['indent'](line);t=line.strip()
  if t=='|':t+=' '+lines[i].strip();i+=1
  if t.startswith('| '):
   while '=>' not in t:t+=' '+lines[i].strip();i+=1
   pattern,rhs=t.split('=>',1);out.append(pad+pattern.strip()+' =>')
   if rhs.strip():out.append(' '*(len(pad)+t.index('=>')+3)+rhs.strip())
  elif t.startswith(('then ','else ')):
   word,rest=t.split(' ',1);out += [pad+word,' '*(len(pad)+len(word)+1)+rest]
  else:out.append(line)
 return out
ns['normalize']=normalize_columns
names=re.findall(r'^def (\S+).*',s,re.M);selected=[n for n in names if not any(x in n for x in ['.closure','.Insts.','_loop']) and any(x in n for x in ['decode_','validate_','transition_kind','require_header'])]
selected.sort(key=lambda n:(n!='pool_v1.pair_forest_terminal.transition_kind',len(n)))
out=[];fail=[]
for i,name in enumerate(selected):
 short='Parser'+str(i).zfill(2)
 try:
  header,result,body,args,explicit=ns['get'](name);node=ns['parse'](ns['normalize'](body));calls=[];emitted=ns['emit'](node,calls=calls).replace('letI : ExternalFuns := ops','letI : ProverRwFull.ExternalFuns := ops')
  text='import AspisR1TerminalDecoder.Funs\nimport R1Z.PV_W_IfLaws\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RJDec_'+short+'\nopen Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws\nvariable [ProverRwFull.ExternalTypes]\n\n'
  text+='def program\n  '+header+' :\n  P '+result+' := do\n'+emitted+'\n\n'
  text+='theorem source (ops : ProverRwFull.ExternalFuns)\n  '+header+' :\n  erase ops (program '+' '.join(explicit)+') =\n    '+name+' '+' '.join(args)+' := by\n  unfold program '+name+'\n'+ns['proof'](node)+'\n\n#print axioms source\nend R1Z.PV_RJDec_'+short+'\n'
  (D/('PV_RJDec_'+short+'.lean')).write_text(text);out.append(dict(module='R1Z.PV_RJDec_'+short,source_function=name,source_pin=pin,body_sha256=hashlib.sha256(body.encode()).hexdigest(),calls=calls))
 except Exception as e:fail.append(dict(function=name,error=repr(e)))
(E/'parser-reification.json').write_text(json.dumps(dict(translator_source_sha256=hashlib.sha256(old.encode()).hexdigest(),modules=out,unsupported=fail,evidence_class='complete Result source reification; native primitive/helper and complete ROMView associations remain obligations'),indent=2)+'\n');print(len(out),'source bodies;',len(fail),'unsupported');print(fail)
