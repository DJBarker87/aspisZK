"""Own focused audit manifests; raw ax2 driver semantics unchanged from NMP."""
from pathlib import Path
import re,json,hashlib,shutil,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx1-observed3-20261110'
mods=['NNG_DRowSpec136','NNG_Model134']
# Explicit current source-fold cone, excluding superseded interface prototypes.
proofs=['NNG_DSourceRoot136','NNG_DSourcePayload136','NNG_DSourceCircleGuard136','NNG_DSourceMark5','NNG_DSourceCircle1','NNG_DSourceBeforeZ1','NNG_DSourceRecord26','NNG_DSourceCircle0','NNG_DSourceState136','NNG_DSourceMark4','NNG_DSourceTerminalGuard','NNG_DSourceAddExtra','NNG_DSourceIndex28','NNG_DSourceAddMask','NNG_DSourceMultiply','NNG_DSourceExtra','NNG_DSourceRecord25','NNG_DSourceMask','NNG_DSourceBlind','NNG_DSourceRow0','NNG_DSourceHigh','NNG_DSourceLow','NNG_DSourceMark3','NNG_DPublicMap136','NNG_DSourceTerminal','NNG_DSourceClaims','NNG_DSourceMark2','NNG_DSourceRounds','NNG_DRowSpec136','NNG_EnvOccurrences136','NNG_Model134','NNG_TreeEmission']
roots=[];selected={}
for m in proofs:
 valid=[]
 for f in E.glob('NNG_L[0-9][0-9][0-9]/receipt.json'):
  d=json.loads(f.read_text())
  if d.get('module')==m and d.get('exit_status')==0:valid.append((f,d))
 assert valid,m
 f,d=sorted(valid)[-1];selected[m]=str(f.relative_to(E))
 roots.extend(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text()))
roots=sorted(set(roots));groups=[roots[i:i+4] for i in range(0,len(roots),4)]
text='import NMQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#print axioms '+n+'\n' for n in roots)
(E/'NNG_FOLD_COMBINED.lean').write_text(text)
(E/'NNG_FOLD_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots,'groups':groups,'selected_receipts':selected},indent=1))
(E/'NNG_FOLD_AUDIT_MODULES.json').write_text(json.dumps([['NNG_FOLD_COMBINED']]*len(groups)))
a=(P/'NMP_generated/NMP_BM_ProofDriver.lean').read_text();b=a.replace('NMP_BM_','NNG_FOLD_')
(E/'NNG_FOLD_ProofDriver.lean').write_text(b)
(E/'NNG_FOLD_DRIVER.diff').write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True))))
(E/'NNG_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:shutil.copyfile(P/'NMP_native'/n,E/'NNG_native'/n)
s=(P/'NMP_BM_link.py').read_text().replace('NMP_BM_','NNG_FOLD_').replace('NMP_native','NNG_native');(E/'NNG_FOLD_link.py').write_text(s)
s=(P/'NMP_BM_audit_batch.py').read_text().replace('NMP_BM_','NNG_FOLD_').replace('NMP_native','NNG_native').replace("['NNG_FOLD_Driver','NNG_FOLD_ProofDriver']","['NNG_FOLD_ProofDriver']")
(E/'NNG_FOLD_audit_batch.py').write_text(s)
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in ['NNG_FOLD_AUDIT_ROOTS.json','NNG_FOLD_AUDIT_MODULES.json','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']}
(E/'NNG_FOLD_AUDIT_MANIFEST_PINS.json').write_text(json.dumps(pins,indent=1))
print(json.dumps({'roots':len(roots),'groups':len(groups)}))
