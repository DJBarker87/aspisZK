from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'tx1-driver2-20261109';Q=E.parent/'tx1-driver-20261108';W=E.parent/'ledger21-20261110'
latest={}
for f in sorted(E.glob('NLJ_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());m=r.get('module')
 if r['kind']!='lean' or r['exit_status'] or not m or m in ['NLJ_Inspect','NLJ_Driver','NLJ_ProofDriver','NLJ_COMBINED_IMPORT']:continue
 src=E/'NLJ_generated'/(m+'.lean');tested=f.parent/'sources/NLJ_generated'/(m+'.lean')
 if src.exists() and tested.exists() and src.read_bytes()==tested.read_bytes():latest[m]=(r,f)
mods=sorted(latest);roots=[]
for m,(r,f) in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
assert 'NLJ_ControlFold' in mods and 'NLJ_Tx1Fold' in mods and 'NLJ_PrepareFold' in mods
text='import NLG_COMBINED_IMPORT\nimport NKQ_COMBINED_IMPORT\nimport NLC_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n-- No CLOSED row roots: conditional source folds only; physical native association remains OPEN.\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
text+='\nset_option pp.proofs false\n'
for n in ['AspisR1.NLJ_Observed.initial_source','AspisR1.NLJ_Observed.events_from_cuts','AspisR1.NLJ_Control137.observed_fold','AspisR1.NLJ_Prepare.fold_from_steps','AspisR1.NLJ_Tx1.source_fold']:
 text+='#print '+n+'\n'
(E/'NLJ_generated/NLJ_COMBINED_IMPORT.lean').write_text(text);(E/'NLJ_COMBINED_IMPORT.lean').write_text(text)
(E/'NLJ_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,selected_receipts={m:str(f.relative_to(E)) for m,(r,f)in latest.items()},unproved_goals=['AspisR1.NLJ_Prepare.SourceEquality','AspisR1.NLJ_Tx1.SourceEquality'],row_roots=[]),indent=2))
allroots=sorted(set(json.loads((W/'NLG_AUDIT_ROOTS.json').read_text())['roots']+json.loads((P/'NLC_AUDIT_ROOTS.json').read_text())['roots']+json.loads((Q/'NKQ_AUDIT_ROOTS.json').read_text())['roots']+roots))
# Same raw ax2 walker, complete root set; 30 balanced groups, ~365 roots each.
# No timeout increase: 180s and unchanged 6G/8G/zero-swap caps. Old groups ~357 roots.
groups=[allroots[len(allroots)*j//30:len(allroots)*(j+1)//30]for j in range(30)]
(E/'NLJ_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups)))
(E/'NLJ_AUDIT_MODULES.json').write_text(json.dumps([['NLJ_COMBINED_IMPORT'] for _ in groups]))
expected={};conflicts=[]
for path in [W/'NLG_EXPECTED_IMPORTS.jsonl',Q/'NKQ_EXPECTED_IMPORTS.jsonl',P/'NLC_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLJ_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLJ_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
s=(E/'NLJ_READONLY_NLI_RowSpec136.lean.txt').read_text()
expected['NLI_RowSpec136']=dict(module='NLI_RowSpec136',imports=list(dict.fromkeys(['Init']+re.findall(r'^import (?:all )?([\w.]+)',s,re.M))))
(E/'NLJ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(P/'NLC_generated'/('NLC_'+name+'.lean')).read_text().replace('NLC_','NLJ_')
 (E/'NLJ_generated'/('NLJ_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(P/('NLC_'+name)).read_text().replace('NLC','NLJ').replace('codex-cx-tx1-driver2-20261109','codex-cx-tx1-prepare-20261110').replace('NLJ_exports_20261109','NLJ_exports_20261110')
 (E/('NLJ_'+name)).write_text(s)
(E/'NLJ_native').mkdir(exist_ok=True);pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 shutil.copyfile(P/'NLC_native'/n,E/'NLJ_native'/n);pins[n]=hashlib.sha256((E/'NLJ_native'/n).read_bytes()).hexdigest()
(E/'NLJ_AUDIT_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
priors={tag:json.loads(lzma.decompress(path.read_bytes())) for tag,path in [('NLG',W/'NLG_CLOSURE_PINS.json.xz'),('NLC',P/'NLC_CLOSURE_PINS.json.xz'),('NKQ',Q/'NKQ_CLOSURE_PINS.json.xz')]}
(E/'NLJ_PREDECESSORS.json.xz').write_bytes(lzma.compress(json.dumps(priors).encode()))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=len(groups),expected_import_conflicts=0)))
