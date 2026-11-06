"""Generate a module import gate and unchanged NFX/ax2 audit consumers."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rs=[json.loads(l) for l in (E/'NLM_ATTEMPTS.jsonl').read_text().splitlines()]
modules=[];roots=[];pending=[];selected={}
for p in sorted(E.glob('NLM_*.lean')):
 m=p.stem
 if any(t in m for t in ['Inspect','Driver','COMBINED_IMPORT']):continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 good=[r for r in rs if r['kind']=='lean' and r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()]
 if not good:pending.append(m);continue
 modules.append(m);selected[m]=good[-1]['attempt']
 source=p.read_text();ns=re.search(r'^namespace ([\w.]+)',source,re.M)
 if ns:roots += [ns[1]+'.'+t for t in re.findall(r'^theorem ([\w]+)',source,re.M)]
assert not pending,('Compile current sources individually first',pending)
roots+=['AspisR1.RPx_Deployed.deployed']
groups=[roots[i:i+8] for i in range(0,len(roots),8)]
(E/'NLM_MODULES.json').write_text(json.dumps(modules,indent=1)+'\n')
(E/'NLM_SOURCE_SELECTORS.json').write_text(json.dumps(selected,indent=1)+'\n')
(E/'NLM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1)+'\n')
imports=['NLG_COMBINED_IMPORT','NLE_COMBINED_IMPORT','NLF_COMBINED_IMPORT']+modules
(E/'NLM_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+'#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
source=Path('evidence/tx2-entry-20261109/NLE_Driver.lean').read_text().replace('NLE_','NLM_')
old='  let (modules, roots) := if mode == "scan" then (#[`NLM_COMBINED_IMPORT], #[]) else (#[], #[])'
new='''  let (modules, roots) ←
    if mode == "fixtures" then
      pure (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else if mode == "scan" then pure (#[`NLM_COMBINED_IMPORT], #[])
    else if mode.startsWith "proof" then do
      let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NLM_AUDIT_ROOTS.json"))
      let groups ← IO.ofExcept (manifest.getObjValAs? (Array (Array String)) "groups")
      let some idx := (mode.drop 5).toString.toNat? | throw (IO.userError "invalid proof mode")
      let some names := groups[idx]? | throw (IO.userError "proof group out of range")
      pure (#[`NLM_COMBINED_IMPORT], names.map String.toName)
    else throw (IO.userError "unknown audit mode")'''
assert old in source
source=source.replace(old,new)
(E/'NLM_ScanDriver.lean').write_text(source)
expected={}
for src in ['evidence/ledger21-20261110/NLG_EXPECTED_IMPORTS.jsonl','evidence/tx2-entry-20261109/NLE_EXPECTED_IMPORTS.jsonl','evidence/sdk-borrow-20261109/NLF_EXPECTED_IMPORTS.jsonl']:
 for line in Path(src).read_text().splitlines():
  r=json.loads(line);m=r['module']
  if m in expected:assert expected[m]==r['imports'],m
  expected[m]=r['imports']
for m in modules+['NLM_COMBINED_IMPORT','NLM_ScanDriver']:
 expected[m]=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NLM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n' for m,im in sorted(expected.items())))
(E/'NLM_batch.py').write_text(Path('evidence/tx2-entry-20261109/NLE_batch.py').read_text().replace('NLE_','NLM_').replace("'NLM_Driver'","'NLM_ScanDriver'").replace("NLM_ProofDriver","NLM_ScanDriver"))
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
