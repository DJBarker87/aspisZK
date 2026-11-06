from pathlib import Path
import json,re,hashlib,subprocess,difflib,lzma
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
(E/'NLF_COMBINED_IMPORT.lean').write_text('import NKW_COMBINED_IMPORT\nimport NJN_COMBINED_IMPORT\nimport NLF_SdkBorrowLaw\n#print axioms AspisR1.RPx_Deployed.deployed\n')
mods=sorted(p.stem for p in E.glob('NLF_*.lean') if p.stem not in ['NLF_COMBINED_IMPORT','NLF_ProofDriver','NLF_ScanDriver'])
ats=[json.loads(l) for l in (E/'NLF_ATTEMPTS.jsonl').read_text().splitlines()]
roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 h=sha((E/(m+'.lean')).read_bytes())
 receipts=[r for r in ats if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert receipts,('CURRENT_SOURCE_NOT_CHECKED',m)
 for line in receipts[-1]['print_axioms']:
  name=re.match("'([^']+)'",line)[1];assert 'sorryAx' not in line
  if name not in roots:roots.append(name)
roots+= [r for r in json.loads((E.parent/'entry-sdk-20261108/NJN_AUDIT_ROOTS.json').read_text())['groups'][0] if r not in roots]
(E/'NLF_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=1)+'\n')
(E/'NLF_AUDIT_MODULES.json').write_text(json.dumps([['NLF_COMBINED_IMPORT']])+'\n')
lines={}
for p in [E.parent/'ledger20-20261109/NKW_EXPECTED_IMPORTS.jsonl',E.parent/'entry-sdk-20261108/NJN_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  x=json.loads(line)
  assert x['module'] not in lines or lines[x['module']]==x,('BASELINE_CONFLICT',x['module'])
  lines[x['module']]=x
for m in mods+['NLF_COMBINED_IMPORT']:
 lines[m]=dict(module=m,imports=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M))
(E/'NLF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(lines[k])+'\n' for k in sorted(lines)))
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
selected=subprocess.check_output(['git','show','HEAD:evidence/slice-q-mul4-20261104/NFA_WALKER.lean'])
assert selected==canonical
pins=dict(walker_source_byte_identical=True,source_sha256=sha(canonical),canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',selected='evidence/slice-q-mul4-20261104/NFA_WALKER.lean',modules=len(mods),new_and_reused_roots=len(roots),driver_diffs=['NLF_ProofDriver.diff','NLF_ScanDriver.diff'])
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=E.parent/'entry-sdk-20261108'/('NJN_'+n+'.xz');raw=lzma.decompress(p.read_bytes())
 (E/('NLF_'+n+'.xz')).write_bytes(p.read_bytes());(E/('NLF_'+n+'.sha256')).write_text(sha(raw)+'\n');pins[n]=sha(raw)
(E/'NLF_WALKER_PIN.json').write_text(json.dumps(pins,indent=1)+'\n')
print('NLF audit manifests prepared: '+str(len(mods))+' modules, '+str(len(roots))+' raw roots')
