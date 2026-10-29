"""Freeze only checked current sources; preserve all other proposals as text."""
from pathlib import Path
import json,re,hashlib
E=Path('evidence/pv-l1d-20261029');plan=json.loads((E/'build-plan.json').read_text())['modules']
accepted={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
drafts=E/'drafts';drafts.mkdir(exist_ok=True);rows=[];theorems=[];roots=[]
for p in sorted(Path('lean').glob('PV_L1D_*.lean')):
 m=p.stem
 if m in ['PV_L1D_Statements','PV_L1D_Axioms','PV_L1D_FocusedReplay']:continue
 b=p.read_bytes();sha=hashlib.sha256(b).hexdigest();ok=m in accepted and accepted[m]['source_sha256']==sha
 if ok and m!='PV_L1D_Inspect':
  roots.append(m)
  for line in accepted[m]['axioms']:
   name=re.match(r"'([^']+)'",line)[1]
   if name not in theorems:theorems.append(name)
  rows.append(dict(module=m,status='checked model; no native producer claim',path=str(p),sha256=sha,source_revision=accepted[m]['source_revision']))
 else:
  dest=drafts/(m+'.lean.txt');p.rename(dest)
  rows.append(dict(module=m,status='diagnostic only' if ok else 'unaccepted draft; zero theorem credit',path=str(dest),sha256=sha,attempted=any(m in json.loads(f.read_text()).get('modules',[]) for f in E.glob('submission-*.json'))))
imports=''.join('import '+m+'\n' for m in roots)+'import PV_RJ4IDB_OpenInputs\nimport PV_DIAG2_ClientRetry\n'
checks=''.join('#check '+m+'\n' for m in theorems)
checks+=''.join('#check PV_RJ4IDB.OpenInputs.'+m+'\n' for m in ['L1_COUNT_TRACE','L1_ORACLE_PREFIX','L1_TIME_TRACE','L1_RETAINED_SIDECHANNELS'])
Path('lean/PV_L1D_Statements.lean').write_text(imports+'/-! Checked MODEL statements only. No concrete native input is installed. -/\n'+checks+'#print axioms PV_L1D_UploadCounts.same_original_result\n')
Path('lean/PV_L1D_Axioms.lean').write_text('import PV_L1D_Statements\n'+''.join('#print axioms '+m+'\n' for m in theorems)+'''#print axioms R1Z.ProverRwRetryModel.retry
#print axioms R1Z.SideChannelL1AttemptRecord.erase_run
#print axioms R1Z.SideChannelEntropyLaw.first_accepted
#print axioms R1Z.SideChannelEntropyLaw.sixteen_exhaustion
#print axioms R1Z.SideChannelRetryLaw.actual_entry_mass
#print axioms PV_DIAG2.source_client_no_rejected
#print axioms PV_RJ4IDB.native_factorization
''')
# EntropyLaw is compiled privately but not necessarily imported by another root.
s=Path('lean/PV_L1D_Axioms.lean').read_text().replace('import PV_L1D_Statements\n','import PV_L1D_Statements\nimport R1Z.SideChannelEntropyLaw\n');Path('lean/PV_L1D_Axioms.lean').write_text(s)
Path('lean/PV_L1D_FocusedReplay.lean').write_text('''import PV_L1D_Axioms
/-! One final focused replay of the accepted count-source closure. This is not
a replay or establishment of the deployed privacy endpoint. -/
#print axioms PV_L1D_UploadCounts.same_original_result
#print axioms PV_L1D_RetryFold.erasure
#print axioms PV_L1D_RetryCount.successful_callbacks
''')
(E/'final-source-manifest.json').write_text(json.dumps(dict(roots=roots,theorems=theorems,sources=rows),indent=2)+'\n')
print('Checked roots',len(roots),'theorems',len(theorems),'drafts',sum('draft' in r['status'] for r in rows))
