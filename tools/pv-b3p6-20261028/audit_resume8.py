"""Freeze accepted current-source declarations; rejected drafts never enter audits."""
from pathlib import Path
import re,json,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume8';entry='884adf0f9d0a199263bbeef2fd18cb6881a4b6cf'
index=json.loads((O/'receipt-index.json').read_text());latest={r['module']:r for r in index if r['exit']==0}
old=set(subprocess.check_output(['git','ls-tree','-r','--name-only',entry,str(L)],text=True).splitlines())
mods=[];records=[];theorems=[];pending=[]
for p in sorted(L.glob('PV_B3P_*.lean')):
 if str(p)in old or p.stem.startswith('PV_B3P_Resume8'):continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest();row=latest.get(p.stem);accepted=row is not None and row['source_sha256']==sha
 if accepted:mods.append(p.stem)
 else:pending.append(dict(module=p.stem,path=str(p),sha256=sha,status='rejected, superseded, or uncompiled; excluded',attempts=[dict(attempt=r['attempt'],exit=r['exit'])for r in index if r['module']==p.stem]))
 for m in re.finditer(r'^theorem (\S+)(.*?)(?:\s*:=|\s*:\s*by)',p.read_text(),re.M|re.S):
  name='PV_B3P_Success227.'+m[1]
  if accepted:theorems.append(name)
  records.append(dict(theorem=name,module=p.stem,path=str(p),source_sha256=sha,statement='theorem '+m[1]+m[2],accepted=accepted,accepting_attempt=row['attempt']if accepted else None,semantic_use='reclassification within existing Charon/Aeneas tool trust; D188 and source binding required before source-law credit; D381/D386 remain pending owner obligations, never T',credit='emitted-Result/supporting law only unless explicitly separately bound'))
assert len(theorems)==len(set(theorems))
for name,data in [('accepted-supporting-modules.json',mods),('theorem-classification.json',records),('audit-theorems.json',sorted(theorems)),('unaccepted-candidates.json',pending)]:
 (O/name).write_text(json.dumps(data,indent=2)+'\n')
# Choose the strongest checked root at this round's actual stopping point.
priority=['PV_B3P_InstalledOk8227','PV_B3P_TerminalOk8227','PV_B3P_CompositionSuccess8227','PV_B3P_SemanticStagesSuccess227','PV_B3P_DigestBridge8227','PV_B3P_HornerBodyBinding8227','PV_B3P_HornerLoopBinding8227']
roots=[m for m in priority if m in mods]
if not roots:roots=mods
keys=[r['theorem']for r in records if r['accepted']and r['module']in roots]
# Import all accepted modules so every accepted declaration has an audit context.
(L/'PV_B3P_Resume8Combined.lean').write_text(''.join('import '+m+'\n'for m in mods)+'\n-- Accepted current-source laws only; no native/source binding inferred.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys)+''.join('#print axioms PV_B3P_Install227.'+n+'\n'for n in ['actual_source','preserved_op224','preserved_op226','preserved_op228']))
(L/'PV_B3P_Resume8Axioms.lean').write_text('import PV_B3P_Resume8Combined\n\n'+''.join('#print axioms '+n+'\n'for n in sorted(theorems)))
(L/'PV_B3P_Resume8Focused.lean').write_text('import PV_B3P_Resume8Axioms\n\n-- One frozen focused replay, not an endpoint release replay.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys))
(O/'focused-manifest.json').write_text(json.dumps(dict(kind='one frozen accepted-law closure; endpoint/native binding separate',modules=mods,roots=['PV_B3P_Resume8Combined','PV_B3P_Resume8Axioms','PV_B3P_Resume8Focused'],strongest_checked_roots=roots,audited_theorems=len(theorems),pending_candidates=pending),indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(mods),audited_theorems=len(theorems),strongest_checked_roots=roots,excluded=len(pending))))
