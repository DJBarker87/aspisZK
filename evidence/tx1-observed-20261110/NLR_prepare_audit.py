from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent
priors=[E.parent/'ledger22-20261110',E.parent/'tx1-prepare-20261110',E.parent/'tx1-driver2-20261109']
tags=['NLO','NLJ','NLC'];latest={}
for f in sorted(E.glob('NLR_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());m=r.get('module')
 if r['kind']!='lean' or r['exit_status'] or not m or m in ['NLR_Inspect','NLR_Driver','NLR_ProofDriver','NLR_COMBINED_IMPORT']:continue
 src=E/'NLR_generated'/(m+'.lean');tested=f.parent/'sources/NLR_generated'/(m+'.lean')
 if src.exists() and tested.exists() and src.read_bytes()==tested.read_bytes():latest[m]=(r,f)
mods=sorted(latest);roots=[]
for m,(r,f)in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
assert 'NLR_PrepareFold' in mods,'Source fold not yet compiled'
text='import NLO_COMBINED_IMPORT\nimport NLJ_COMBINED_IMPORT\nimport NLC_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'\nset_option pp.proofs false\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
for n in ['AspisR1.NLJ_Control137.observed_fold','AspisR1.NLR_Prepare.source','AspisR1.NLR_Prepare.source_fold','AspisR1.NLR_Interface.RowSpec_137','AspisR1.NLR_Interface.RowSpec_087']:text+='#print '+n+'\n'
(E/'NLR_generated/NLR_COMBINED_IMPORT.lean').write_text(text);(E/'NLR_COMBINED_IMPORT.lean').write_text(text)
(E/'NLR_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,selected_receipts={m:str(f.relative_to(E))for m,(r,f)in latest.items()},row_roots=[]),indent=2))
allroots=set(roots)
for path,tag in zip(priors,tags):allroots.update(json.loads((path/(tag+'_AUDIT_ROOTS.json')).read_text())['roots'])
allroots=sorted(allroots);groups=[allroots[len(allroots)*j//30:len(allroots)*(j+1)//30]for j in range(30)]
(E/'NLR_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups)))
(E/'NLR_AUDIT_MODULES.json').write_text(json.dumps([['NLR_COMBINED_IMPORT']for _ in groups]))
expected={};conflicts=[]
for path,tag in zip(priors,tags):
 for line in (path/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLR_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLR_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NLR_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n'for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(priors[1]/'NLJ_generated'/('NLJ_'+name+'.lean')).read_text().replace('NLJ_','NLR_')
 (E/'NLR_generated'/('NLR_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(priors[1]/('NLJ_'+name)).read_text().replace('NLJ','NLR').replace('codex-cx-tx1-prepare-20261110','codex-cx-tx1-observed-20261110')
 (E/('NLR_'+name)).write_text(s)
(E/'NLR_native').mkdir(exist_ok=True);pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 shutil.copyfile(priors[1]/'NLJ_native'/n,E/'NLR_native'/n);pins[n]=hashlib.sha256((E/'NLR_native'/n).read_bytes()).hexdigest()
(E/'NLR_AUDIT_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
priorpins={tag:json.loads(lzma.decompress((path/(tag+'_CLOSURE_PINS.json.xz')).read_bytes()))for tag,path in zip(tags,priors)}
(E/'NLR_PREDECESSORS.json.xz').write_bytes(lzma.compress(json.dumps(priorpins).encode()))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=len(groups),expected_import_conflicts=0)))
