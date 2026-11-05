from pathlib import Path
import json,re,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent

def read(p):
 p=Path(p)
 return p.read_text() if p.exists() else subprocess.check_output(['git','show','HEAD:'+str(p)],text=True)

# Explicit top-level theorem roots from the job's accepted source files.
roots=[]
for p in sorted(E.glob('NHT_*.lean')):
 if p.stem.endswith('Driver'):continue
 s=p.read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if ns:roots += [ns[1]+'.'+x for x in re.findall(r'^theorem (\w+)',s,re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
groups=[roots[i:i+10] for i in range(0,len(roots),10)]
(E/'NHT_AUDIT_ROOTS.json').write_text(json.dumps({'groups':groups},indent=1)+'\n')
base={};pins={};repairs=[]
for src in ['tx2-model-20261106/NHQ_EXPECTED_IMPORTS.jsonl','slice-d-pair-20261106/NHI_EXPECTED_IMPORTS.jsonl','extract-stage-20261106/NHR_EXPECTED_IMPORTS.jsonl']:
 p=E.parent/src
 try:s=read(p)
 except subprocess.CalledProcessError:continue
 pins[str(p)]=hashlib.sha256(s.encode()).hexdigest()
 for line in s.splitlines():
  row=json.loads(line)
  if row['module']=='NGC_MemoryLimit' and row['imports']==['Init','all']:
   repairs.append({'input':str(p),'original':row.copy(),'reason':'NHI baseline parser captured import-all keyword; source-backed NHQ baseline is canonical'})
   assert base.get('NGC_MemoryLimit',{}).get('imports')==['Init','Lean.Shell']
   row={'module':'NGC_MemoryLimit','imports':['Init','Lean.Shell']}
  if row['module'] in base and base[row['module']]['imports']!=row['imports']:raise ValueError('incompatible baselines '+row['module'])
  base[row['module']]=row
for p in E.glob('NHT_*.lean'):
 base[p.stem]={'module':p.stem,'imports':['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)}
# Raw parameterized NHR sources were absent from NHQ's earlier baseline.
for fn in ['tx2_common','tx2_authenticated']:
 for kind in ['Types','Funs']:
  p=E.parent/f'extract-stage-20261106/NHR_lean/NHR_{fn}/{kind}.lean'
  base[f'NHR_{fn}.{kind}']={'module':f'NHR_{fn}.{kind}','imports':['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)}
(E/'NHT_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in base.values()))
(E/'NHT_IMPORT_BASELINES.json').write_text(json.dumps({'pins':pins,'repairs':repairs},indent=1)+'\n')

original=read('evidence/axaudit2-20261102/NEP_Driver.lean')
# Preserve the complete audit/import/kernel code. Only module/root lists and
# allowed runtime setup differ; source diff committed for ax2 condition2.
start=original.index('  let (modules, roots) :=');end=original.index('  let env ←',start)
selection='''  let (modules, roots) := if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
'''
for i,g in enumerate(groups):
 selection+=f'    else if mode == "proof{i}" then\n      (#[`NHT_COMBINED_IMPORT], #['+', '.join('`'+x for x in g)+'])\n'
selection+='    else (#[], #[])\n'
proof=original[:start]+selection+original[end:]
proof=proof.replace('import NEP_WALKER','import NFA_WALKER\nimport NFA_MemoryLimit').replace('  enableInitializersExecution','  NFA_MemoryLimit.set\n  initSearchPath (← findSysroot)\n  enableInitializersExecution')
assert proof[proof.index('  let env ←'):]==original[original.index('  let env ←'):]
(E/'NHT_ProofDriver.lean').write_text(proof)
(E/'NHT_ProofDriver.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),proof.splitlines(True),fromfile='NEP_Driver.lean',tofile='NHT_ProofDriver.lean')))
scan=read(E.parent/'tx2-model-20261106/NHQ_Driver.lean').replace('NHQ','NHT')
(E/'NHT_Driver.lean').write_text(scan)
batch=read(E.parent/'tx2-model-20261106/NHQ_batch.py').replace('NHQ','NHT')
(E/'NHT_batch.py').write_text(batch)
native=E/'NHT_native';native.mkdir(exist_ok=True)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 (native/name).write_text(read(E.parent/'tx2-model-20261106/NHQ_native'/name))
walker=read('evidence/axaudit2-20261102/NEP_WALKER.lean')
actual=read('evidence/slice-q-mul4-20261104/NFA_WALKER.lean')
assert walker==actual
(E/'NHT_AUDIT_PROVENANCE.json').write_text(json.dumps({'walker_source':'evidence/axaudit2-20261102/NEP_WALKER.lean','walker_sha256':hashlib.sha256(walker.encode()).hexdigest(),'resolved_module':'NFA_WALKER','byte_identical':True,'driver_audit_suffix_byte_identical':True,'driver_base_sha256':hashlib.sha256(original.encode()).hexdigest(),'proof_driver_sha256':hashlib.sha256(proof.encode()).hexdigest(),'scan_base':'evidence/tx2-model-20261106/NHQ_Driver.lean','scan_change':'prefix-only paths/module root; NFX method unchanged'},indent=1)+'\n')
print(json.dumps({'roots':len(roots),'groups':len(groups),'baselines':len(base)}))
