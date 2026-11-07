"""Build audit inputs from CURRENT successful new-module receipts only."""
from pathlib import Path
import hashlib,json,re,shutil,difflib
E=Path(__file__).resolve().parent
latest={}
for p in sorted(E.glob('NMP_L[0-9][0-9][0-9]/receipt.json')):
 if int(p.parent.name[-3:])<81:continue
 r=json.loads(p.read_text());m=r.get('module','');src='NMP_generated/'+m.replace('.','/')+'.lean'
 if r['kind']!='lean' or r['exit_status']!=0 or not (E/src).is_file():continue
 q=p.parent/'sources'/src
 if q.is_file() and q.read_bytes()==(E/src).read_bytes():latest[m]=(r,p)
required={'NMP_ObservedSource','NMP_PrepareSource','NMP_CanonicalFold137','NMP_CanonicalFold087'}
assert required<=set(latest),sorted(required-set(latest))
modules=sorted(m for m in latest if not m.startswith('NMP_BM_') and m!='NMP_COMBINED_IMPORT')
roots_by_module={}
for m in modules:
 r,p=latest[m]
 raw=(p.parent/'stdout.log').read_text()
 roots=sorted(set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",raw)))
 assert not any('sorryAx' in line for line in raw.splitlines() if 'axioms' in line),m
 if roots:roots_by_module[m]=roots
roots=sorted({r for rs in roots_by_module.values() for r in rs})
headline='AspisR1.RPx_Deployed.deployed'
text='import NLX_COMBINED_IMPORT\nimport NLZ_COMBINED_IMPORT\nimport NLR_COMBINED_IMPORT\nimport NLJ_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+'\n'
for root in roots+[headline]:text+='#print axioms '+root+'\n'
(E/'NMP_generated/NMP_BM_COMBINED_IMPORT.lean').write_text(text)
(E/'NMP_BM_COMBINED_IMPORT.lean').write_text(text)
(E/'NMP_COMBINED_IMPORT.lean').write_text(text)
(E/'NMP_generated/NMP_COMBINED_IMPORT.lean').write_text(text)
# Every new top is audited once; no unchanged full regression is repeated.
groups=[];imports=[]
for m,rs in roots_by_module.items():
 if m=='NMP_ObservedStoppedPrefix':groups.append(rs);imports.append([m])
 elif m=='NMP_Transport_T0':groups.append(rs);imports.append([m])
 elif m=='NMP_PrepareCallerBounds':groups.append(rs);imports.append([m])
 elif m=='NMP_UsizeExact':groups.append(rs[:2]);imports.append([m]);groups.extend([[r] for r in rs[2:]]);imports.extend([[m] for r in rs[2:]])
 elif m=='NMP_DirectBind':groups.append(rs[:2]);imports.append([m]);groups.append(rs[2:]);imports.append([m])
 else:
  for r in rs:groups.append([r]);imports.append([m])
groups.append([headline]);imports.append(['NMP_COMBINED_IMPORT'])
assert 171+len(groups)-1<=267,('Reserve277-280 for final receipts/export',len(groups))
(E/'NMP_BM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots+[headline],groups=groups),indent=1)+'\n')
(E/'NMP_BM_AUDIT_MODULES.json').write_text(json.dumps(imports,indent=1)+'\n')
(E/'NMP_BM_MODULES.json').write_text(json.dumps(dict(modules=modules,roots=roots,selected_receipts={m:str(latest[m][1].relative_to(E)) for m in modules},row_roots=[],qualification='Complete source/value folds and conditional relational folds; no canonical row candidate'),indent=1)+'\n')
expected={}
for dirname,tag in [('tx1-observed2-20261110','NLZ'),('ledger24-20261110','NLX')]:
 for line in (E.parent/dirname/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  row=json.loads(line);m=row['module']
  assert m not in expected or expected[m]['imports']==row['imports'],m
  expected[m]=row
sources={m:E/'NMP_generated'/(m.replace('.','/')+'.lean') for m in modules}
S=E.parent/'tx1-owned-20261111'
for m in ['NMT_CallTree','NMT_TransportBase','NMT_tx1.Types','NMT_RSL_Base','NMT_RSL_Verifier','NMT_RSL_TX1_136','NMT_RSL_TX1_137','NMT_RSL_TX1_087']:sources[m]=S/(m+'.lean')
sources['NMP_COMBINED_IMPORT']=E/'NMP_COMBINED_IMPORT.lean'
for m,p in sources.items():
 names=['Init']+re.findall(r'^import (?:all )?([\w.]+)',p.read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(names)))
(E/'NMP_BM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n'for m in sorted(expected)))
for stem in ['Driver','ProofDriver']:
 p=E/'NMP_generated'/('NMP_'+stem+'.lean');raw=p.read_text();new=raw.replace('NMP_','NMP_BM_').replace('NMP_BM_COMBINED_IMPORT','NMP_COMBINED_IMPORT')
 (E/'NMP_generated'/('NMP_BM_'+stem+'.lean')).write_text(new)
 (E/('NMP_BM_'+stem+'.diff')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),new.splitlines(True),fromfile=p.name,tofile='NMP_BM_'+stem+'.lean')))
(E/'NMP_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:shutil.copyfile(E.parent/'tx1-observed2-20261110/NLZ_native'/n,E/'NMP_native'/n)
inputs=['NMP_BM_AUDIT_ROOTS.json','NMP_BM_AUDIT_MODULES.json','NMP_BM_EXPECTED_IMPORTS.jsonl','NMP_native/NFA_WALKER.c','NMP_native/NFA_MemoryLimit.c']
(E/'NMP_BM_AUDIT_MANIFEST_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in inputs},indent=1)+'\n')
print(json.dumps(dict(current_modules=len(modules),new_roots=len(roots),audit_scopes=len(groups),row_roots=0)))
