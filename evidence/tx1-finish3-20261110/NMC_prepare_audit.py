"""Owned support-gate inputs; imports are modules, never private source names."""
from pathlib import Path
import json,re,lzma,hashlib,shutil,difflib
E=Path(__file__).resolve().parent
bases=[('NLS',E.parent/'ledger23-20261110'),('NLU',E.parent/'tx1-finish2-20261110'),('NLI',E.parent/'tx1-finish-20261110'),('NLH',E.parent/'terminal6-20261110')]
latest={}
for p in sorted(E.glob('NMC_L*/receipt.json'),key=lambda p:int(p.parent.name[-3:])):
 x=json.loads(p.read_text());m=x.get('module','');src=E/'NMC_generated'/(m+'.lean');snap=p.parent/'sources/NMC_generated'/(m+'.lean')
 if x.get('kind')=='lean'and x['exit_status']==0 and src.exists()and snap.exists()and src.read_bytes()==snap.read_bytes()and not m.startswith('NMC_Inspect'):
  latest[m]=(x,p)
assert 'NMC_Transcription'in latest
roots=[]
for m,(x,p)in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(p.parent/'stdout.log').read_text())
roots=sorted(set(roots));mods=sorted(latest)
s=''.join('import '+tag+'_COMBINED_IMPORT\n'for tag,_ in bases)+''.join('import '+m+'\n'for m in mods)+'\n-- SUPPORT ONLY; no full136 fold/root or ledger credit.\n'
for name in ['AspisR1.RPx_Deployed.deployed']+roots:s+='#print axioms '+name+'\n#check @'+name+'\n'
(E/'NMC_generated/NMC_COMBINED_IMPORT.lean').write_text(s);(E/'NMC_COMBINED_IMPORT.lean').write_text(s)
allroots=[];expected={};conflicts=[]
for tag,base in bases:
 allroots+=json.loads((base/(tag+'_AUDIT_ROOTS.json')).read_text())['roots']
 for line in(base/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  row=json.loads(line);old=expected.get(row['module'])
  if old and set(old['imports'])!=set(row['imports']):conflicts.append(dict(module=row['module'],before=old,after=row))
  expected[row['module']]=row
assert not conflicts,conflicts
allroots=list(dict.fromkeys(allroots+roots));groups=[allroots[i::30]for i in range(30)]
(E/'NMC_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups)))
(E/'NMC_AUDIT_MODULES.json').write_text(json.dumps([['NMC_COMBINED_IMPORT']for _ in groups]))
for m in mods+['NMC_COMBINED_IMPORT']:
 source=(E/'NMC_generated'/(m+'.lean')).read_text();imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',source,re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NMC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in expected.values()))
driver_diff=''
for name in ['Driver','ProofDriver']:
 original=(E.parent/'tx1-finish2-20261110/NLU_generated'/('NLU_'+name+'.lean')).read_text()
 source=original.replace('NLU','NMC')
 (E/'NMC_generated'/('NMC_'+name+'.lean')).write_text(source)
 driver_diff+=''.join(difflib.unified_diff(original.splitlines(True),source.splitlines(True),fromfile='NLU_'+name+'.lean',tofile='NMC_'+name+'.lean'))
(E/'NMC_DRIVER.diff').write_text(driver_diff)
(E/'NMC_native').mkdir(exist_ok=True)
cpins={}
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=E.parent/'tx1-finish2-20261110/NLU_native'/name;shutil.copyfile(p,E/'NMC_native'/name);cpins[name]=hashlib.sha256(p.read_bytes()).hexdigest()
(E/'NMC_AUDIT_INPUT_PINS.json').write_text(json.dumps(cpins,indent=2)+'\n')
(E/'NMC_PATHS.json').write_text(json.dumps(json.loads((E/'NMC_ENV.json').read_text())['LEAN_PATH'].split(':')))
priors={tag:json.loads(lzma.decompress((base/(tag+'_CLOSURE_PINS.json.xz')).read_bytes()))for tag,base in bases if(base/(tag+'_CLOSURE_PINS.json.xz')).exists()}
assert {'NLS','NLU','NLI'}<=set(priors)
# NLH publishes exports, not a standalone closure manifest. Check every NLH
# object selected by the coherent predecessor closure against that export.
nlh=json.loads((E.parent/'terminal6-20261110/NLH_EXPORT.json').read_text())
exported={r['name'][:-6].replace('/','.') : r['sha256']for r in nlh['files']if r['name'].endswith('.olean')}
selected={r['module']:r['sha256']for prior in priors.values()for r in prior['selected_objects']if r['module'].startswith('NLH_')and r['path'].endswith('.olean')}
missing=[m for m,h in selected.items()if exported.get(m)!=h]
assert not missing,missing
(E/'NMC_NLH_CLOSURE_COVERAGE.json').write_text(json.dumps(dict(status='PASS_NLH_SELECTED_EXPORTS',selected_modules=len(selected),mismatches=[],basis='NLS/NLU/NLI coherent closures plus NLH_EXPORT; NLH has no standalone CLOSURE_PINS',unused_export_modules=sorted(set(exported)-set(selected))),indent=2)+'\n')
blob=json.dumps(priors).encode();(E/'NMC_PREDECESSORS.json.xz').write_bytes(lzma.compress(blob));(E/'NMC_PREDECESSORS.json.sha256').write_text(hashlib.sha256(blob).hexdigest()+'\n')
(E/'NMC_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,row_roots=[],status='SUPPORT_ONLY',groups=30),indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=30,expected_import_conflicts=0)))
