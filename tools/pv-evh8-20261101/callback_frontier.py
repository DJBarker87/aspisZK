"""Inspect reached Result operator callbacks, keeping ignored-argument drop OPEN."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh8-20261101');rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
a=ast.parse(Path('tools/pv-world-20261028/reify-recursive.py').read_text());g=dict(s=s.replace('\npartial_fixpoint',''),re=re)
exec(compile(ast.Module(body=[n for n in a.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['indent','normalize','Node','parse','get']],type_ignores=[]),'<source-parser>','exec'),g)
rows=[]
def walk(node,spine):
 if node.kind=='bind':walk(node.expr,spine);walk(node.next,spine)
 elif node.kind=='let':walk(node.next,spine)
 elif node.kind=='if':walk(node.yes,spine);walk(node.no,spine)
 elif node.kind=='match':
  for _,child in node.branches:walk(child,spine)
 elif node.kind=='call' and node.expr.split()[0] in ['core.result.Result.map','core.result.Result.map_err']:
  expr=' '.join(node.expr.split());label,inst,*rest=expr.split()
  row=dict(spine=spine,operator=label,call=expr)
  if label.endswith('map_err'):
   fn=inst.lstrip('(')+'.call_once';h,r,b,_,_=g['get'](fn)
   row.update(callback=fn,header=h,result=r,body=b,body_sha256=hashlib.sha256(b.encode()).hexdigest(),native_status='OPEN ignored error argument/capture drop and actual operator binding, even if constructor body is pure')
  else:row.update(callback='host_commitment.PrivateSalts.new',native_status='OPEN actual op11 binding; pure constructor checked separately')
  rows.append(row)
for pin in json.load(open(E/'native-preflight.json'))['records']:
 x=json.load(open(pin['path']));_,_,b,_,_=g['get'](x['function']);walk(g['parse'](g['normalize'](b)),pin['name'])
x=dict(status='TEXTUAL callback source inventory only',source=p,revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),callbacks=rows,rows_removed=[])
out=json.dumps(x,indent=2)+'\n';q=E/'callback-frontier.json'
if '--check' in sys.argv:assert q.read_text()==out
else:q.write_text(out)
print('Callback source sites:',len(rows),'; native drops/operator bindings remain OPEN')
