"""Replay the recorded deployed 1.9.0 world/cursor laws in this cohort.
Only imports/namespaces change. Never load the incompatible RDCD dictionaries.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
rev='3972c0274bce3eb3dbe1ca6d911eb6242b6b1628'
sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads(subprocess.check_output(['git','show','HEAD:evidence/pv-rdcd-20261028/resume-final-fingerprint.json']))
parts=[];pins=[]
for suffix in ['World','Trace','Cursor']:
 name='R1Z/PV_RDCD_Zero'+suffix;v=x['modules'][name]
 raw=subprocess.check_output(['git','show',rev+':'+v['path']]);assert sha(raw)==v['sha256']
 text=raw.decode()
 text='\n'.join(l for l in text.splitlines() if not l.startswith('import '))+'\n'
 for s in ['World','Trace','Cursor']:text=text.replace('R1Z.PV_RDCD_Zero'+s,'PV_EVH_DeployedZero'+s).replace('PV_RDCD_Zero'+s,'PV_EVH_DeployedZero'+s)
 parts.append(text);pins.append(dict(module=name,revision=rev,path=v['path'],sha256=v['sha256']))
body='import PV_EVH_ZeroizeArray\n'+''.join(parts)
p=Path('lean/PV_EVH_DeployedZeroWorld.lean')
record=dict(evidence_class='source-identical replay of deployed zeroize 1.9.0 law; imports and namespaces renamed',pins=pins,source_sha256=sha(body.encode()),cache='RDCD cache absent; its Result dictionary cohort conflicts and is NOT imported',structural_source='evidence/pv-rdcd-20261028/zeroize190-complete-structural.json',rows=['V221','V222'],limits=['compiler V370 retained','valid exclusive u8 region required','no register/spill/copy erasure or L3 completion'])
if '--check' in sys.argv:
 assert p.read_text()==body
 assert json.load(open(E/'zero-law-replay.json'))==record
else:
 p.write_text(body);(E/'zero-law-replay.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS source-identical deployed zeroize law replay')

v=x['modules']['R1Z/PV_RDCD_ZeroSelected']
raw=subprocess.check_output(['git','show',rev+':'+v['path']]);assert sha(raw)==v['sha256']
text=raw.decode().replace('import R1Z.PV_RDCD_ZeroWorld','import PV_EVH_DeployedZeroWorld')
text=text.replace('R1Z.PV_RDCD_ZeroSelected','PV_EVH_DeployedZeroSelected').replace('PV_RDCD_ZeroWorld','PV_EVH_DeployedZeroWorld')
p=Path('lean/PV_EVH_DeployedZeroSelected.lean')
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
print('PASS source-identical deployed zeroize selected-law replay')

r=dict(module='R1Z/PV_RDCD_ZeroSelected',revision=rev,path=v['path'],recorded_sha256=v['sha256'],replayed_sha256=sha(text.encode()),edits=['import world law from this cohort','namespace renaming only'],no_old_dictionary_objects_loaded=True)
p=E/'zero-selected-replay.json'
if '--check' in sys.argv:assert json.load(open(p))==r
else:p.write_text(json.dumps(r,indent=2)+'\n')
