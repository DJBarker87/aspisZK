"""Parameterize every external hole; preserve candidate005 concrete emitted bodies."""
from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2]
G=D/'selected64-generated005';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
N='ProverRwRngExtractorselected64';P='ProverRwRngExtractor005'
def decls(p):
 return [(m[1],m[2].strip()) for m in re.finditer(r'\baxiom\s+([\w.]+)([\s\S]*?)(?=\n/--|\Z)',p.read_text())]
pre='import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnoncomputable section\nnamespace '+N+'\n'
ts=decls(G/'TypesExternal_Template.lean');t=pre+'class TypeLeaves where\n'
for i,(n,s) in enumerate(ts):t+=f'  t{i} {s}\n'
t+='variable [TypeLeaves]\n'
for i,(n,s) in enumerate(ts):t+=f'abbrev {n} := @TypeLeaves.t{i} _\n'
body=(G/'Types.lean').read_text().split('namespace '+N+'\n',1)[1]
body=re.sub(r'@\[discriminant isize\]\n','',body)
t+=body
fs=decls(G/'FunsExternal_Template.lean')
f='import R1Z.'+P+'Types\n'+pre.split('\n',1)[1]+'variable [TypeLeaves]\nclass LocalLeaves where\n'
for i,(n,s) in enumerate(fs):f+=f'  f{i} {s}\n'
f+='variable [LocalLeaves]\n'
for i,(n,s) in enumerate(fs):f+=f'def {n} := @LocalLeaves.f{i} _ _\n'
f+=(G/'Funs.lean').read_text().split('namespace '+N+'\n',1)[1]
outputs={P+'Types.lean':t,P+'Emission.lean':f}
for n,s in outputs.items():
 assert not (L/n).exists()
 (L/n).write_text(s)
record=dict(inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in G.iterdir() if p.is_file()},outputs={n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()},type_parameters=ts,function_parameters=fs,changes=['all external holes explicit type/function dictionary parameters, uninstalled; no new axioms','combine split files, remove unused discriminant attributes and generated resource overrides; concrete bodies unchanged'],provider_boundary='No state/events in fill signature; no native installation or effect equivalence claimed')
(D/'adaptation005.json').write_text(json.dumps(record,indent=2)+'\n')
