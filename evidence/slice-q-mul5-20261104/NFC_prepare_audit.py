from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent
latest={}
for p in sorted(E.glob('NFC_L*/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0 and r['module'].startswith('NFC_') and r['module']!='NFC_FinalAudit' and r['print_axioms']:
  latest[r['module']]=r
roots=[];modules=[];pins=[]
for name,r in sorted(latest.items()):
 p=E/(name+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest();assert h in r['source_hashes'].values(),name
 modules.append(name)
 names=re.findall(r"'([^']+)'",'\n'.join(r['print_axioms']));roots.extend(names)
 pins.append(dict(module=name,source_sha256=h,attempt=r['attempt'],theorems=names))
assert len(roots)==len(set(roots));assert len(roots)>=38
s='-- Standalone NFC forest; joint headline import failed in NFC_L058.\n'+''.join('import '+m+'\n' for m in modules)+'\n'+''.join('#print axioms '+n+'\n' for n in roots)
if '--check' in sys.argv:assert (E/'NFC_FinalAudit.lean').read_text()==s
else:(E/'NFC_FinalAudit.lean').write_text(s)
groups=[[] for _ in range(38)]
for i,root in enumerate(roots):groups[i%38].append(root)
manifest=dict(modules=modules,roots=roots,groups=groups,source_pins=pins)
if '--check' in sys.argv:assert json.loads((E/'NFC_PROOF_ROOTS.json').read_text())==manifest
else:(E/'NFC_PROOF_ROOTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(modules),'modules;',len(roots),'top roots;',len(groups),'bounded raw-audit groups')
