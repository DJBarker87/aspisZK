"""Read-only focused target dependency inventory, excluding nested comments."""
from pathlib import Path
import subprocess,json,ast,shlex,hashlib
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw19-resume-20261026'
tree=ast.parse(Path(__file__).with_name('attempt.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='imports');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'imports','exec'),ns);imports=ns['imports']
files=[r/p for p in subprocess.check_output(['rg','--files','docs/research','-g','*.lean'],cwd=r,text=True).splitlines()];by={}
for p in files:by.setdefault(p.name,[]).append(p)
base=r/'docs/research/v8-r0-zk-20261009/lean';generated=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023';sources={};unresolved={}
def resolve(name):
 if name in sources:return sources[name]
 retained=r/'evidence/pv-rw19-resume-20261026/retained-source-inputs'/(name+'.lean.txt')
 if retained.is_file():sources[name]=retained;return retained
 p=base/(name.replace('.','/')+'.lean')
 if p.is_file():sources[name]=p;return p
 if name.startswith('R1Z.ProverRwFull') and (generated/(name.split('.')[-1]+'.lean')).is_file():p=generated/(name.split('.')[-1]+'.lean');sources[name]=p;return p
 candidates=by.get(name.split('.')[-1]+'.lean',[]);exact=[p for p in candidates if str(p).endswith(name.replace('.','/')+'.lean')]
 choices=exact or candidates
 if len(choices)==1:sources[name]=choices[0];return choices[0]
 if choices and len({hashlib.sha256(p.read_bytes()).hexdigest() for p in choices})==1:sources[name]=choices[0];return choices[0]
 unresolved[name]=[str(p.relative_to(r)) for p in choices];return None
seen=set();order=[]
def visit(name):
 if name in seen:return
 seen.add(name);p=resolve(name)
 if p:
  for dep in imports(p.read_text()):visit(dep)
 order.append(name)
for target in ['R1Z.ProverRw18AxiomsAudit','R1Z.ProverRw19P6RawContextIdentity','R1Z.ProverRw19P6ContextIdentity','R1Z.ProverRw19P6Join','R1Z.ProverRw19P6Caller','R1Z.ProverRw19AuditCaller','R1Z.ProverRw19AssemblyLength','R1Z.ProverRw19ReferenceLength','R1Z.ProverRw19MathematicalAssembly']:visit(target)
code="""from pathlib import Path
import sys,json
names=json.load(sys.stdin);j=Path('/home/dombarker/project-offloads/aspis-joint-20261019');env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[j/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
print(json.dumps({n:next((str(r/(n.replace('.','/')+'.olean')) for r in roots if (r/(n.replace('.','/')+'.olean')).is_file()),None) for n in names}))
"""
q=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(order),text=True,capture_output=True,check=True);cache=json.loads(q.stdout)
rows=[{'module':n,'cached':cache[n],'source':str(sources[n].relative_to(r)) if n in sources else None,'imports':imports(sources[n].read_text()) if n in sources else None} for n in order]
(e/'focused-dependencies.json').write_text(json.dumps({'classification':'read-only focused target inventory, not a manifest replay','order':rows,'unresolved':unresolved},indent=2)+'\n')
missing=[x for x in rows if not x['cached']];ready=[x for x in missing if x['imports'] is not None and all(cache.get(v) for v in x['imports'])]
print(json.dumps({'missing':len(missing),'missing_with_source':sum(bool(x['source']) for x in missing),'ready':ready[:12],'first_missing':[x['module'] for x in missing[:15]]},indent=2))
