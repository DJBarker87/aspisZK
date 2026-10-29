"""Freeze supporting-law audit roots from successful current-source receipts only."""
from pathlib import Path
import re,json,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume7';entry='1b86d5a589e710a7c48c726c27392aa200e72223'
index=json.loads((O/'receipt-index.json').read_text());latest={r['module']:r for r in index if r['exit']==0}
old=set(subprocess.check_output(['git','ls-tree','-r','--name-only',entry,str(L)],text=True).splitlines())
mods=[];records=[];theorems=[];pending=[]
for p in sorted(L.glob('PV_B3P_*.lean')):
 if str(p)in old or p.stem.startswith('PV_B3P_Resume7'):continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest();row=latest.get(p.stem);accepted=row is not None and row['source_sha256']==sha
 if accepted:mods.append(p.stem)
 else:pending.append(dict(module=p.stem,path=str(p),sha256=sha,status='rejected or uncompiled; not included in audit',latest_attempts=[dict(attempt=r['attempt'],exit=r['exit'])for r in index if r['module']==p.stem]))
 for m in re.finditer(r'^theorem (\S+)(.*?)(?:\s*:=|\s*:\s*by)',p.read_text(),re.M|re.S):
  name='PV_B3P_Success227.'+m[1]
  if accepted:theorems.append(name)
  records.append(dict(theorem=name,module=p.stem,path=str(p),source_sha256=sha,statement='theorem '+m[1]+m[2],accepted=accepted,accepting_attempt=row['attempt']if accepted else None,semantic_use='Rust interpretation is reclassification within existing Charon/Aeneas tool trust; compiler/runtime semantics remain pending D381/D386, never T',credit='supporting mathematical/emitted-Result law only; no full native binding or endpoint premise removal'))
assert len(theorems)==len(set(theorems))
(O/'accepted-supporting-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
(O/'theorem-classification.json').write_text(json.dumps(records,indent=2)+'\n')
(O/'audit-theorems.json').write_text(json.dumps(sorted(theorems),indent=2)+'\n')
(O/'unaccepted-candidates.json').write_text(json.dumps(pending,indent=2)+'\n')
roots=['PV_B3P_CopySuccess227','PV_B3P_PoseidonSuccess227','PV_B3P_SemanticCallersSuccess227']
assert all(m in mods for m in roots)
key=['copy_success','total_reference_poseidon_evaluate_state_only_poseidon_oracle_projected','preweighted_total','total_reference_terminal_add_digest_binding','total_reference_terminal_add_schedule_lanes','total_reference_terminal_add_path_lanes','total_reference_terminal_add_value_lanes','total_reference_terminal_add_occupancy_lanes']
(L/'PV_B3P_Resume7Combined.lean').write_text('\n'.join('import '+m for m in roots)+'\n\n-- Supporting stages only. Full composition_parts/reference/installed Ok witnesses remain open.\n'+ '\n'.join('#check PV_B3P_Success227.'+n+'\n#print axioms PV_B3P_Success227.'+n for n in key)+'\n')
(L/'PV_B3P_Resume7Axioms.lean').write_text('import PV_B3P_Resume7Combined\n\n'+'\n'.join('#print axioms '+n for n in sorted(theorems))+'\n')
(L/'PV_B3P_Resume7Focused.lean').write_text('import PV_B3P_Resume7Axioms\n\n-- One final replay of this frozen supporting closure, not a release endpoint replay.\n'+'\n'.join('#check PV_B3P_Success227.'+n+'\n#print axioms PV_B3P_Success227.'+n for n in key)+'\n')
(O/'focused-manifest.json').write_text(json.dumps(dict(kind='frozen supporting-law closure; full endpoint and full reference not established',modules=mods,roots=['PV_B3P_Resume7Combined','PV_B3P_Resume7Axioms','PV_B3P_Resume7Focused'],audited_theorems=len(theorems),pending_candidates=pending),indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(mods),audited_theorems=len(theorems),unaccepted=pending)))
