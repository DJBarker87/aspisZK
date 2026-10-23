from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2e-20261023';H='/home/dombarker/project-offloads/codex-cx-s2e-20261023';HOST='dombarker@100.108.41.90'
for mode in ['default','devnet','pool']:
 for suffix in ['command','pin']:
  subprocess.run(['scp',HOST+':'+H+'/S2E-sbf-'+mode+'-'+suffix+'.json',str(E)],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['scp',HOST+':'+H+'/S2E-devnet-programs.json',str(E)],check=True,stdout=subprocess.DEVNULL)
for name in ['S2E-reference','S2E-steps']:
 subprocess.run(['scp',HOST+':'+H+'/'+name+'/Cargo.lock',str(E/(name+'-Cargo.lock'))],check=True,stdout=subprocess.DEVNULL)
# Read-only artifact fingerprints. No binary/object/ELF is downloaded or committed.
config=json.loads((E/'lean-022.json').read_text())
remote='''from pathlib import Path
import json,hashlib,os
H=Path("'''+H+'''")
def info(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
roots='''+repr(config['env']['LEAN_PATH'].split(':'))+'''
roots=[H if r=='.' else Path(r) for r in roots]
objects={}
for module in ['S2E_Types','S2E_Model','S2E_SuccessInversion','S2E_Execution','S2E_SdkReuse','S2E_Certificate','S2OwnedStage1TypesV1','S2SdkOwnedTypesV1','S2SdkOwnedModelV1','Aeneas']:
 candidates=[r/(module.replace('.','/')+'.olean') for r in roots if (r/(module.replace('.','/')+'.olean')).exists()]
 assert candidates,module
 objects[module]=dict(selected=info(candidates[0]),alternatives=[info(p) for p in candidates[1:]])
tools=[Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'),Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon-driver'),Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]
tools=[info(p) for p in tools if p.exists()]
llbc=H/'S2E_Reference.llbc';j=json.loads(llbc.read_text())
crates={}
base=H.parent/'codex-cx-repin-s6-20261020/src/crates'
for crate in ['aspis-core','aspis-statement','aspis-r1-cost-probe']:
 crates[crate]=[info(p) for p in sorted((base/crate).rglob('*')) if p.is_file() and p.suffix in ['.rs','.toml'] and 'target' not in p.parts]
gotos=[info(p) for p in sorted((H/'kani-target').rglob('*.out'))]
print(json.dumps(dict(objects=objects,tools=tools,llbc={**info(llbc),'has_errors':j['has_errors']},reference_dependency_sources=crates,goto_artifacts=gotos,qualification='Exact selected direct custom objects and tool/input fingerprints; external transitive library closure reuses the named predecessor manifests, not a new coherent frozen release replay. Prior attempt dependency descriptions were incomplete fingerprints; final export audit uses this explicit pinned overlay.'),indent=2))
'''
raw=subprocess.check_output(['ssh',HOST,'python3','-'],input=remote,text=True)
(E/'S2E-host-pins.json').write_text(raw+'\n')
# The byte-identical local SDK specification's verified contract is reused explicitly.
for filename in ['kani-003/receipt.json','final-objects-and-tools.json']:
 p=D/'evidence/s2a-20261023'/filename
 print(filename,hashlib.sha256(p.read_bytes()).hexdigest())
