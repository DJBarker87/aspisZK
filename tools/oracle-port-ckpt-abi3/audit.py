#!/usr/bin/env python3
"""Check scoped proof evidence without rerunning Lean, Kani or full regression."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/ckpt-abi3-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((E/'manifest.json').read_text())
current=[a for a in manifest['attempts'] if a.get('final_current')]
required={'OraclePortCkptAbi3Sections','OraclePortCkptAbi3StdInspection','OraclePortCkptAbi3Canonical','OraclePortCkptAbi3OwnedIter','OraclePortCkptAbi3S10Boundary','OraclePortCkptAbi3Freeze'}
assert {a['module'] for a in current}==required
for a in current:
 assert a['exit']==0 and a['swaps']==0
 p=B/'lean'/(a['module'].replace('.','/')+'.lean')
 assert sha(p)==a['source_sha256'],p
 assert '-M4400' in a['argv'] and '-j1' in a['argv']
 for line in a['axioms']:
  names=re.search(r'\[([\s\S]*?)\]',line)
  if names:assert all(n.strip() in {'propext','Classical.choice','Quot.sound'} for n in names[1].replace('\n','').split(',')),line
 assert not a['errors']
freeze=next(a for a in current if a['module']=='OraclePortCkptAbi3Freeze')
assert len(freeze['axioms'])==17,freeze['axioms']
new_lean=list((B/'lean').glob('OraclePortCkptAbi3*.lean'))
for p in new_lean:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|^set_option max(?:Heartbeats|RecDepth)',p.read_text(),re.M),p
roots=[]
for name in ['raw','wide','qm31','query','semantic','weight','lengths-writer','lengths-reader']:
 p=E/'host/receipts'/(name+'-v1');d=json.loads((p/'receipt.json').read_text())
 assert d['exit_status']==0 and d['swaps']==0
 assert 'VERIFICATION SUCCESSFUL' in (p/'stdout.log').read_text()
 assert '--unwinding-assertions' in d['target']
 assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert d['cgroup_swap_peak_bytes']==0
 assert d['source_sha256']['tools/oracle-port-ckpt-abi3/src/lib.rs']==sha(p/'source.rs.txt')
 # Earlier section roots predate the additive length-root include. Validate
 # exact root source identity against its retained snapshot, never relabel it.
 source=(R/'tools/oracle-port-ckpt-abi3/src/lib.rs').read_text()
 if not name.startswith('lengths-'):
  source=source.replace('\ninclude!("length-proofs.rs");\n','')
 assert hashlib.sha256(source.encode()).hexdigest()==sha(p/'source.rs.txt')
 for key,expected in d['source_sha256'].items():
  if key.endswith('.rs') and key!='tools/oracle-port-ckpt-abi3/src/lib.rs':
   assert sha(R/key)==expected,key
 roots.append(dict(root=name,receipt=str((p/'receipt.json').relative_to(R)),sha256=sha(p/'receipt.json')))
pins=json.loads((E/'source-pins.json').read_text())
assert not pins['validation']['mismatches']
for path,meta in pins['pins'].items():assert sha(R/path)==meta['sha256'],path
reuse=json.loads((E/'reused-codec-contracts.json').read_text())
assert reuse['specs_helpers_contracts_and_contract_roots_identical']
for row in reuse['receipts']:assert sha(R/row['receipt'])==row['receipt_sha256']
dep=json.loads((E/'driver-obligations.json').read_text())
assert dep['s10_report']['imported'] and not dep['accepted_run_join']
for p in dep['s10_report']['imported_paths']:
 expected=subprocess.check_output(['git','show',dep['research_revision']+':'+p],cwd=R)
 assert (R/p).read_bytes()==expected,p
changed=subprocess.check_output(['git','diff','6881031b8','--name-only','--','crates','programs'],cwd=R,text=True).splitlines();assert not changed
result=dict(schema='checkpoint-abi3-focused-audit-v1',source_revision=freeze['source_revision'],current_lean_targets=[a['module'] for a in current],authored_theorems=sum(len(re.findall(r'^theorem ',p.read_text(),re.M)) for p in new_lean),final_axiom_reports=len(freeze['axioms']),final_kani_targets=roots,standard_axioms_only=True,shipped_changes=changed,elf_rebuild_required=False,complete_checkpoint_cone=False,accepted_run_join=False,whole_reader_certified=False,physical_allocation_established=False,full_frozen_manifest_replayed=False)
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
