from pathlib import Path
import json,re,lzma,hashlib
E=Path(__file__).resolve().parent
read=lambda p:p.read_text()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes()).decode()
mods=sorted(p.stem for p in E.glob('NMO_*.lean')if p.stem not in ['NMO_Driver','NMO_ProofDriver','NMO_COMBINED_IMPORT'])
latest={}
for p in E.glob('NMO_L*/receipt.json'):
 x=json.loads(p.read_text());m=x.get('module');src=E/(str(m)+'.lean');snap=p.parent/'sources'/(str(m)+'.lean')
 if x.get('kind')=='lean'and x['exit_status']==0 and src.exists()and snap.exists()and src.read_bytes()==snap.read_bytes():latest[m]=(x,p)
assert set(mods)<=set(latest),dict(unchecked=sorted(set(mods)-set(latest)))
roots=sorted(set(n for m in mods for n in re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",read(latest[m][1].parent/'stdout.log'))))
assert all(n.startswith('AspisR1.NMO_')for n in roots)
combined=''.join('import '+m+'\n'for m in ['NLX_COMBINED_IMPORT','NMC_COMBINED_IMPORT','NLU_COMBINED_IMPORT','NLI_COMBINED_IMPORT','NLH_COMBINED_IMPORT']+mods)
combined+='\n-- SUPPORT GATE ONLY: TX1:136 has no candidate root.\n'
for n in ['AspisR1.RPx_Deployed.deployed']+roots:combined+='#print axioms '+n+'\n#check @'+n+'\n'
(E/'NMO_COMBINED_IMPORT.lean').write_text(combined)
expected={};conflicts=[]
for tag,base in [('NLX','ledger24-20261110'),('NMC','tx1-finish3-20261110'),('NLU','tx1-finish2-20261110'),('NLI','tx1-finish-20261110'),('NLH','terminal6-20261110')]:
 p=E.parent/base/(tag+'_EXPECTED_IMPORTS.jsonl')
 if not p.exists():continue
 for l in p.read_text().splitlines():
  row=json.loads(l);old=expected.get(row['module'])
  if old and old['imports']!=row['imports']:conflicts.append(dict(module=row['module'],before=old,after=row))
  expected[row['module']]=row
assert not conflicts,conflicts
for m in mods+['NMO_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NMO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in expected.values()))
(E/'NMO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots+['AspisR1.RPx_Deployed.deployed'],groups=[roots,['AspisR1.RPx_Deployed.deployed']]),indent=2)+'\n')
(E/'NMO_AUDIT_MODULES.json').write_text(json.dumps([['NMO_COMBINED_IMPORT'],['NMO_COMBINED_IMPORT']]))
(E/'NMO_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,row_roots=[],status='SUPPORT_ONLY'),indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),row_roots=0,expected_import_conflicts=0)))
