from pathlib import Path
import json,re,subprocess
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
roots=[R/'lean',R/'docs/research/100bit-spend-path-20261013/lean']
lookup={}
for root in roots:
 for p in root.rglob('*.lean'):
  key=p.stem;lookup.setdefault(key,p)
seen={}
def visit(m):
 if m in seen or m.startswith(('Aeneas','Mathlib','Lean','Std','Batteries')):return
 p=lookup.get(m.split('.')[-1]);seen[m]=str(p.relative_to(R)) if p else None
 if p:
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    for n in line[7:].split():visit(n)
visit('RawActualAnnotatedPolynomialRowAgreementConsumer')
paths=json.loads((P/'FIq_001.json').read_text())['env']['LEAN_PATH'].split(':')
code='from pathlib import Path;import json;mods='+repr(list(seen))+';paths='+repr(paths)+';print(json.dumps({m:next((str(Path(p)/(m.replace(".","/")+".olean")) for p in paths if (Path(p)/(m.replace(".","/")+".olean")).exists()),None) for m in mods}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],capture_output=True,text=True,check=True)
obj=json.loads(r.stdout);out={m:{'source':p,'object':obj[m]} for m,p in seen.items()}
(P/'FIq_semantic-preflight.json').write_text(json.dumps(out,indent=2)+'\n')
print('closure',len(out),'missing',sum(v['object'] is None for v in out.values()))
for m,v in out.items():
 if v['object'] is None:print(m,v['source'])
