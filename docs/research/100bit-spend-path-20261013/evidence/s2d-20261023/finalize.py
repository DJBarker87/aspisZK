#!/usr/bin/env python3
"""Receipt/source/axiom audit only. Never launches a prover or regression."""
from pathlib import Path
import hashlib,json,re,subprocess
base=Path(__file__).resolve().parent
root=next(p for p in base.parents if (p/'programs/r1-cost-probe/src/lib.rs').exists())
lean=root/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(base/'audit.py'),'--check'],check=True)
accepted={'lean-001','lean-002','lean-004','kani-002'}
rows=[]
for p in sorted(base.glob('*/receipt.json')):
 r=json.loads(p.read_text()); attempt=r['attempt']; assert attempt in accepted or attempt in {'lean-003','kani-001'}
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for name,h in r['source_hashes'].items():
  src=lean/name if name.endswith('.lean') else base/name
  if attempt=='lean-003' and name=='S2D_Cleanup.lean': src=base/'failed-sources/S2D_Cleanup_lean003.lean'
  assert sha(src)==h,(attempt,name)
 if attempt in accepted:
  assert r['exit_status']==0
  if r['kind']=='lean':
   for line in r['print_axioms']:
    assert 'sorryAx' not in line,line
    if 'depends on axioms:' in line:
     assert set(re.search(r'\[([^]]*)\]',line).group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'}
   module=lean/r['sources'][0]
   text=module.read_text()
   theorems=re.findall(r'^theorem (\w+)',text,re.M)
   assert all('#print axioms '+t in text for t in theorems)
   assert len(theorems)==len(r['print_axioms'])
   assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', '\n'.join(l for l in text.splitlines() if not l.startswith('#print')))
  else:
   assert '** 0 of 3 failed' in (p.parent/'stdout.log').read_text()
 rows.append({**r,'status':'accepted local evidence' if attempt in accepted else 'excluded failure','receipt':str(p.relative_to(base))})
changed=subprocess.check_output(['git','diff','--name-only','0accd8700d893bc85f8be7b201143fd95aeb7a19'],cwd=root,text=True).splitlines()
assert all(p.startswith('docs/research/100bit-spend-path-20261013/') for p in changed)
assert not any(p.startswith(('programs/','crates/')) for p in changed)
summary=dict(schema='focused-extractor-proof-packet-v1',claim='S2-D local E-indexed error algebra, trusted borrow case/drop lemmas, verbatim release observer None; native enclosing refinement NOT established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip(),attempts=rows,budget=dict(lean_used=4,lean_limit=100,kani_invocations_used=2,kani_limit=60),tool_pins=json.loads((base/'tool-pins.json').read_text()),shipped_files_changed=False,elf_rebuild='not triggered; no new ELF certification',replay='receipt audit only; no repeated full regression',native_certificate='uninstantiated; E and original input indices are not source provenance')
(base/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
print('receipt/source/axiom audit passed: 3 Lean modules and 1 Kani harness accepted; 2 failures excluded')
