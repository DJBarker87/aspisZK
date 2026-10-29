"""Freeze the accepted current-source set once, after focused targets finish."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume15';L=D/'lean';rows=json.loads((O/'receipt-index.json').read_text());latest={}
for r in sorted(rows,key=lambda r:r['attempt']):latest[r['module']]=r
accepted={m:r for m,r in latest.items()if r['exit']==0 and (L/(m+'.lean')).is_file()and hashlib.sha256((L/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256']}
# Every function is either proven under these exact source hashes or explicitly
# uncredited; failed source hashes cannot enter this final frozen import set.
mods=sorted(accepted);names=[]
for m,r in accepted.items():
 for line in r['print_axioms']:
  match=re.match(r"'([^']+)'",line)
  if match:names.append(match[1])
names=sorted(set(names));assert names
imports=''.join('import '+m+'\n'for m in mods)
combined='''-- Exact accepted resume15 source cohort, frozen after focused checks.
'''+imports+'\n#check PV_B3P_Correct14227.selected_callback14\n'
# Explicitly check the new model bridge only if its complete module passed.
for mod,decl in [('PV_B3P_JointBridge15227','PV_B3P_Bridge15227.selected_callback15'),('PV_B3P_FieldsVecCaller15227','PV_B3P_Fields15227.fields_vec_cursor_projection15'),('PV_B3P_TerminalFrame15227','PV_B3P_Terminal15227.source_preserved_op261_15')]:
 if mod in accepted:combined+='#check '+decl+'\n'
(L/'PV_B3P_Resume15Combined.lean').write_text(combined)
(L/'PV_B3P_Resume15Axioms.lean').write_text('import PV_B3P_Resume15Combined\n'+''.join('#print axioms '+n+'\n'for n in names))
focused='''import PV_B3P_Resume15Combined
-- One final replay of this frozen focused manifest. This does not rebuild the
-- unchanged privacy endpoint, Rust artifacts or the peer-owned catalogue.
'''
for n in names:focused+='#check '+n+'\n'
(L/'PV_B3P_Resume15Focused.lean').write_text(focused)
manifest=dict(modules=mods,theorems=names,hashes={m:accepted[m]['source_sha256']for m in mods},focused_replay_count=1,new_native_associations_claimed=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(O/'focused-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(mods),audited_theorems=len(names))))
