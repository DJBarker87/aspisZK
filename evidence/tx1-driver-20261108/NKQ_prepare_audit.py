"""Own audit staging: unchanged NKN algorithms; prefix/path substitutions only."""
from pathlib import Path
import json,re,hashlib,lzma,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger19-20261108'
latest={}
for f in sorted(E.glob('NKQ_L[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(f.read_text())
 if j['kind']=='lean' and j.get('module'):latest[j['module']]=(j,f)
excluded={'NKQ_Inventory','NKQ_LibraryInspect','NKQ_ScalarInspect'}
mods=sorted(m for m,(j,f) in latest.items() if j['exit_status']==0 and m not in excluded)
assert 'NKQ_FinishSlots' in mods and 'NKQ_FinishMaskDomain' in mods
roots=[]
for m in mods:
 j,f=latest[m];raw=(f.parent/'stdout.log').read_text()
 roots += re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",raw)
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
text='import NKN_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'\n-- Source support and domains only; no promotion of TX1:136/137/087/094.\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#print '+n+'\n'
(E/'NKQ_generated/NKQ_COMBINED_IMPORT.lean').write_text(text);(E/'NKQ_COMBINED_IMPORT.lean').write_text(text)
(E/'NKQ_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,excluded=sorted(excluded)),indent=2)+'\n')
a=json.loads((P/'NKN_AUDIT_ROOTS.json').read_text());a['groups'].append(roots+[headline]);a['roots']=a['roots']+roots+[headline]
(E/'NKQ_AUDIT_ROOTS.json').write_text(json.dumps(a,indent=1)+'\n')
(E/'NKQ_AUDIT_MODULES.json').write_text(json.dumps([['NKQ_COMBINED_IMPORT'] for _ in a['groups']],indent=1)+'\n')
expected=[json.loads(l)for l in (P/'NKN_EXPECTED_IMPORTS.jsonl').read_text().splitlines()];known={x['module']for x in expected}
for m in mods+['NKQ_COMBINED_IMPORT']:
 assert m not in known
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NKQ_generated'/f'{m}.lean').read_text(),re.M)
 expected.append(dict(module=m,imports=list(dict.fromkeys(imports))))
(E/'NKQ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n'for x in expected))
for name in ['ProofDriver','Driver']:
 old=(P/f'NKN_{name}.lean').read_text();new=old.replace('NKN_','NKQ_')
 (E/'NKQ_generated'/f'NKQ_{name}.lean').write_text(new)
 (E/f'NKQ_{name}_ADAPTATION.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NKN_'+name,tofile='NKQ_'+name)))
raw=(P/'NKN_CLOSURE_PINS.json.xz').read_bytes();(E/'NKQ_PREDECESSOR_PINS.json.xz').write_bytes(raw)
old=(P/'NKN_pin.py').read_text();new=old.replace('NKN_','NKQ_').replace("json.loads((B/'NKQ_PREDECESSOR_PINS.json').read_text())","json.loads(lzma.decompress((B/'NKQ_PREDECESSOR_PINS.json.xz').read_bytes()))")
new=new.replace("/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKQ_20261108/NKQ_exports_20261108","/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108/NKQ_exports_20261108")
(E/'NKQ_pin.py').write_text(new)
(E/'NKQ_pin_ADAPTATION.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NKN_pin.py',tofile='NKQ_pin.py')))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),all_roots=len(a['roots']),groups=len(a['groups']))))
