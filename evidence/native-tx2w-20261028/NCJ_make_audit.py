from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
root=E.parent.parent
latest={}
for p in sorted(E.glob('NCJ_L*/receipt.json')):
 r=json.loads(p.read_text());cfg=json.loads((E/(p.parent.name+'.json')).read_text());m=cfg['module']
 if r['exit_status']==0:latest[m]=(p,r)
green={};unproved=[]
for p in sorted((root/'lean').glob('NCJ_*.lean')):
 if p.stem=='NCJ_FinalAudit':continue
 item=latest.get(p.stem)
 if item:
  receipt,r=item;old=receipt.parent/'sources/NCJ_generated'/p.name
  if old.exists() and old.read_bytes()==p.read_bytes():
   green[p.stem]={'receipt':str(receipt.relative_to(root)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'axioms':r['print_axioms']};continue
 unproved.append(str(p.relative_to(root)))
unproved += [str(p.relative_to(root)) for p in sorted(E.glob('NCJ_*_UNPROVED.lean.txt'))]
audit=('import KMX_CopyMeaning\n' if '--copy' in __import__('sys').argv else '')+''.join('import '+m+'\n' for m in green)+'set_option autoImplicit false\n'
for m,row in green.items():
 for line in row['axioms']:
  name=line.split("'")[1]
  if name.startswith('NCJ_'):audit+='#print axioms '+name+'\n'
(root/'lean/NCJ_FinalAudit.lean').write_text(audit)
(E/'NCJ_FINAL_INDEX.json').write_text(json.dumps(dict(green_modules=green,unproved_drafts=unproved),indent=2)+'\n')
print('Audit inputs',len(green),'green modules;',len(unproved),'unproved drafts')
# The final slot also checks two small copy-frame laws after the unchanged
# KMX dependency has been compiled independently. No dependent native bridge
# is credited from these value-only laws.
import sys
if '--copy' in sys.argv:
 p=root/'lean/NCJ_CopyFrames.lean'
 if not p.exists():p=E/'NCJ_CopyFrames_RELOCATED_TO_FINAL_AUDIT.lean.txt'
 body=p.read_text().split('\n',1)[1]
 with (root/'lean/NCJ_FinalAudit.lean').open('a') as f:f.write('\n'+body)
