"""Splice checked parser subprograms in dependency order; leave real opaque leaves explicit."""
from pathlib import Path
import json,re,subprocess,ast,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rjdec-20261028'
x=json.loads((E/'parser-reification.json').read_text());mods={v['source_function']:v for v in x['modules']};plan=json.loads((E/'build-plan.json').read_text());pin=plan['modules']['AspisR1TerminalDecoder.Funs'];s=subprocess.check_output(['git','show','HEAD:'+pin['path']],text=True)
old=subprocess.check_output(['git','show','HEAD:tools/pv-world-20261028/reify-recursive.py'],text=True);nodes=[n for n in ast.parse(old).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))];ns=dict(re=re,json=json,s=s);exec(compile(ast.Module(body=nodes,type_ignores=[]),'pinned-world-translator','exec'),ns)
# Read only the column-preserving normalizer from our generator.
new=ast.parse((R/'tools/pv-rjdec-20261028/reify-decoders.py').read_text());local={'ns':ns};exec(compile(ast.Module(body=[n for n in new.body if isinstance(n,ast.FunctionDef)],type_ignores=[]),'parser-layout','exec'),local);ns['normalize']=local['normalize_columns']
graph={n:sorted({c['label'] for c in v['calls'] if c['label'] in mods and c['label']!=n}) for n,v in mods.items()};order=[];visited=set()
def topo(n):
 if n in visited:return
 visited.add(n)
 for c in graph[n]:topo(c)
 if graph[n]:order.append(n)
for n in mods:topo(n)
active={n:(mods[n]['module'].replace('Parser','ParserR') if graph[n] else mods[n]['module']) for n in mods};rawemit=ns['emit'];rawproof=ns['proof']
def emit(node,n=2,calls=None):
 if node.kind=='call':
  expr=node.expr;label=expr.split()[0]
  if label in mods:
   calls.append(dict(label=label,spliced=active[label]));return ns['spaces'](active[label]+'.program '+expr[len(label):].strip(),n)
 return rawemit(node,n,calls)
def proof(node,n=2):
 if node.kind=='call':
  expr=node.expr;label=expr.split()[0]
  if label in mods:return ns['spaces']('exact '+active[label]+'.source ops '+expr[len(label):].strip(),n)
 return rawproof(node,n)
ns['emit']=emit;ns['proof']=proof
out=[]
for name in order:
 v=mods[name];mod=active[name]
 if mod in ['R1Z.PV_RJDec_ParserR12','R1Z.PV_RJDec_ParserR15']:
  out.append(dict(module=mod,source_function=name,chunked=True));continue
 short=mod.split('.')[-1];header,result,body,args,explicit=ns['get'](name);node=ns['parse'](ns['normalize'](body));calls=[]
 imports=['AspisR1TerminalDecoder.Funs','R1Z.PV_W_IfLaws']+[active[c] for c in graph[name]]
 text=''.join('import '+m+'\n' for m in imports)+'set_option autoImplicit false\nnoncomputable section\nnamespace '+mod+'\nopen Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws\nvariable [ProverRwFull.ExternalTypes]\n\n'
 text+='def program\n  '+header+' :\n  P '+result+' := do\n'+emit(node,calls=calls).replace('letI : ExternalFuns := ops','letI : ProverRwFull.ExternalFuns := ops')+'\n\n'
 text+='theorem source (ops : ProverRwFull.ExternalFuns)\n  '+header+' :\n  erase ops (program '+' '.join(explicit)+') =\n    '+name+' '+' '.join(args)+' := by\n  unfold program '+name+'\n'+proof(node)+'\n\n#print axioms source\nend '+mod+'\n'
 (D/(short+'.lean')).write_text(text);out.append(dict(module=mod,source_function=name,spliced=graph[name],calls=calls))
(E/'recursive-parsers.json').write_text(json.dumps(dict(modules=out,order=[v['module'] for v in out]),indent=2)+'\n');print(len(out),'dependent source parsers')
