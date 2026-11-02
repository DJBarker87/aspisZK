"""Read-only missing-object plan for the isolated accumulator model shell."""
import subprocess,json,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent
roots=json.loads((E/'NEI_L096.json').read_text())['env']['LEAN_PATH'].split(':')
code='from pathlib import Path\nimport json\nroots='+repr(roots)+'\nprint(json.dumps(sorted(set(str(p.relative_to(Path(root)))[:-6].replace("/",".") for root in roots for p in Path(root).rglob("*.olean") if p.is_file()))))'
existing=set(json.loads(subprocess.check_output(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True)))
paths=set(subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines());nodes={};order=[];absent=[]
def visit(name):
 if name in existing or name in nodes:return
 ps=[f'docs/research/100bit-spend-path-20261013/lean/{name}.lean',f'lean/{name}.lean']
 path=next((p for p in ps if p in paths),None)
 if path is None:absent.append(name);return
 text=subprocess.check_output(['git','show','HEAD:'+path],text=True);deps=[m for l in text.splitlines() if l.startswith('import ') for m in l[7:].split()]
 nodes[name]=dict(path=path,source_sha256=hashlib.sha256(text.encode()).hexdigest(),imports=deps,text=text)
 for d in deps:visit(d)
 order.append(name)
visit('NBO_AccumulateAssociation')
out=dict(order=order,absent=absent,sources=nodes)
(E/'NEI_ACCUM_PREREQUISITE_PLAN.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(missing_count=len(order),order=order,absent=absent)))
