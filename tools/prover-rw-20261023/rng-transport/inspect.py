"""Read-only selected source inventory. No extractor or build is run."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-transport'
E.mkdir(exist_ok=True)
remote=r'''
from pathlib import Path
import hashlib,json,subprocess
T=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain')
C=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon/charon/src')
S=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
items=[(T/'aeneas-full/src/llbc/TypesAnalysis.ml',[(300,490),(780,830)]),(T/'aeneas-full/src/interp/InterpStatements.ml',[(20,58),(975,1000)]),(T/'aeneas-full/src/interp/InterpExpressions.ml',[(149,170),(570,604)]),(C/'ast/expressions.rs',[(350,375)]),(C/'ast/ullbc_ast.rs',[(120,150)]),(C/'ast/types.rs',[(1,1)]),(S/'num/niche_types.rs',[(1,52),(115,130)]),(S/'num/nonzero.rs',[(115,130)]),(S/'result.rs',[(960,973)])]
out=[]
for p,spans in items:
 b=p.read_bytes();lines=b.decode().splitlines();out.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),excerpts=[dict(first=a,last=z,text='\n'.join(lines[a-1:z])) for a,z in spans]))
# Exact Copy implementations and LLBC pattern declarations, retaining line numbers.
for p,terms in [(S/'num/nonzero.rs',['Copy for','Clone for']),(C/'ast/types.rs',['TPattern','Pattern','Range(']),(C/'ast/llbc_ast.rs',['Drop','StorageDead','Deinit'])]:
 b=p.read_bytes();ls=b.decode().splitlines();out.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),matches=[dict(line=i+1,text='\n'.join(ls[max(0,i-3):i+6])) for i,l in enumerate(ls) if any(t in l for t in terms)]))
bins=[]
for p in [T/'output/aeneas-b59d5188-lean432-extended-static',Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'),Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon-driver')]:
 b=p.read_bytes();bins.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
print(json.dumps(dict(sources=out,binaries=bins),indent=2))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True,capture_output=True,check=True)
v=json.loads(p.stdout);v['command']=['ssh','dombarker@100.108.41.90','python3 -'];v['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();v['assessment']='Read-only source excerpts and current tool hashes, not a new extraction or release identity gate. Backend source directory includes accepted extensions; source association to selected failure is corroborative, not a reproducible binary build.'
(E/'source-inspection.json').write_text(json.dumps(v,indent=2)+'\n')
llbc=R/'tools/prover-rw-20261023/rng-caller/ProverRwRngCaller.llbc';data=json.loads(llbc.read_text())['translated']
selected={k:[x for x in data[k] if x is not None and any(t in json.dumps(x['item_meta']['name']) for t in ['NonZero','map_err','selected_callback','StateOnlyAttemptEntropyError','getrandom'])] for k in ['type_decls','fun_decls']}
selected.update(target_information=data['target_information'],options=data['options'],llbc_sha256=hashlib.sha256(llbc.read_bytes()).hexdigest(),assessment='Reused prototype extraction, not actual secure factory extraction. Complete selected declarations retained; primitive library opaque bodies remain absent.')
(E/'selected-llbc.json').write_text(json.dumps(selected,indent=2)+'\n')
print('Retained selected source and LLBC inventories')
