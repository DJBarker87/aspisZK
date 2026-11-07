"""Own audit inputs; preserve the existing walker and NFX scan semantics."""
from pathlib import Path
import json,re,hashlib,shutil,sys,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx1-observed-20261110';L=E.parent/'ledger23-20261110'
groups=int(sys.argv[1]);latest={}
for p in sorted(E.glob('NLZ_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());m=r.get('module','');s=E/'NLZ_generated'/(m+'.lean');q=p.parent/'sources/NLZ_generated'/(m+'.lean')
 if r['kind']=='lean' and r['exit_status']==0 and s.is_file() and q.is_file() and s.read_bytes()==q.read_bytes():latest[m]=(r,p)
mods=sorted(latest);roots=[]
for m,(r,p)in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(p.parent/'stdout.log').read_text())
roots=sorted(set(roots));assert 'NLZ_SegmentChain087'in mods and 'NLZ_SegmentChain137'in mods
text='import NLS_COMBINED_IMPORT\nimport NLR_COMBINED_IMPORT\nimport NLJ_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'\nset_option pp.proofs false\n'
for n in ['AspisR1.RPx_Deployed.deployed']+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
for n in ['AspisR1.NLZ_Segments137.fold','AspisR1.NLZ_Segments087.fold','AspisR1.NLZ_Interface.RowSpec_137','AspisR1.NLZ_Interface.RowSpec_087']:text+='#print '+n+'\n'
(E/'NLZ_generated/NLZ_COMBINED_IMPORT.lean').write_text(text);(E/'NLZ_COMBINED_IMPORT.lean').write_text(text)
(E/'NLZ_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,selected_receipts={m:str(p.relative_to(E))for m,(r,p)in latest.items()},row_roots=[]),indent=2))
allroots=set(roots)
for d,tag in [(P,'NLR'),(L,'NLS')]:allroots.update(json.loads((d/(tag+'_AUDIT_ROOTS.json')).read_text())['roots'])
allroots=sorted(allroots);split=[allroots[len(allroots)*j//groups:len(allroots)*(j+1)//groups]for j in range(groups)]
(E/'NLZ_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=split)))
(E/'NLZ_AUDIT_MODULES.json').write_text(json.dumps([['NLZ_COMBINED_IMPORT']for _ in split]))
expected={};conflicts=[]
for d,tag in [(P,'NLR'),(L,'NLS')]:
 for line in (d/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(line)
  if x['module']in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLZ_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLZ_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NLZ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[k])+'\n'for k in sorted(expected)))
for name in ['Driver','ProofDriver']:
 s=(P/'NLR_generated'/('NLR_'+name+'.lean')).read_text().replace('NLR_','NLZ_');(E/'NLZ_generated'/('NLZ_'+name+'.lean')).write_text(s)
diff=''
for name in ['Driver','ProofDriver']:
 a=(P/'NLR_generated'/('NLR_'+name+'.lean')).read_text();b=(E/'NLZ_generated'/('NLZ_'+name+'.lean')).read_text();diff+=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='NLR_'+name+'.lean',tofile='NLZ_'+name+'.lean'))
(E/'NLZ_DRIVER_DIFF.patch').write_text(diff)
(E/'NLZ_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:shutil.copyfile(P/'NLR_native'/n,E/'NLZ_native'/n)
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in ['NLZ_AUDIT_ROOTS.json','NLZ_AUDIT_MODULES.json','NLZ_EXPECTED_IMPORTS.jsonl','NLZ_native/NFA_WALKER.c','NLZ_native/NFA_MemoryLimit.c']}
(E/'NLZ_AUDIT_MANIFEST_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=groups,expected_import_conflicts=0)))
