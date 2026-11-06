from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'tx1-driver2-20261109';W=E.parent/'ledger21-20261110'
latest={}
for f in E.glob('NLI_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(f.read_text());m=r.get('module')
 if r['kind']!='lean' or r['exit_status'] or not m or m=='NLI_Inspect':continue
 src=E/'NLI_generated'/(m+'.lean');tested=f.parent/'sources/NLI_generated'/(m+'.lean')
 if src.exists() and tested.exists() and src.read_bytes()==tested.read_bytes():latest[m]=(r,f)
mods=sorted(latest);roots=[]
for m,(r,f) in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
assert 'NLI_SourceEquality' in mods, 'Exact FinishSourceEquality must compile before gate'
text='import NLG_COMBINED_IMPORT\nimport NLC_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n-- No row credit before next ledger gate; exact submitted scope in handoff.\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
(E/'NLI_generated/NLI_COMBINED_IMPORT.lean').write_text(text);(E/'NLI_COMBINED_IMPORT.lean').write_text(text)
(E/'NLI_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,proved_source_goal='AspisR1.NLI_Source.finishSourceEquality',unproved_goal='TX1:136 full native parent realization',row_roots=[]),indent=2))
a=json.loads((W/'NLG_AUDIT_ROOTS.json').read_text());all_old=set(a['roots'])
extra=[x for x in json.loads((P/'NLC_AUDIT_ROOTS.json').read_text())['roots']+roots if x not in all_old];extra=sorted(set(extra));a['roots']=a['roots']+extra
# Smaller independently scoped groups than predecessor; unchanged complete root set.
last=max(int(p.parent.name[5:8]) for p in E.glob('NLI_L[0-9][0-9][0-9]/receipt.json'))
groupcount=150-last-8
assert groupcount>=34, 'Reserve all combined/driver/fixture/scan/close scopes'
a['groups']=[a['roots'][i::groupcount] for i in range(groupcount)]
(E/'NLI_AUDIT_ROOTS.json').write_text(json.dumps(a));(E/'NLI_AUDIT_MODULES.json').write_text(json.dumps([['NLI_COMBINED_IMPORT'] for _ in a['groups']]))
expected={};conflicts=[]
for path in [W/'NLG_EXPECTED_IMPORTS.jsonl',P/'NLC_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLI_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLI_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NLI_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(P/'NLC_generated'/('NLC_'+name+'.lean')).read_text().replace('NLC_','NLI_')
 (E/'NLI_generated'/('NLI_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(P/('NLC_'+name)).read_text().replace('NLC','NLI').replace('codex-cx-tx1-driver2-20261109','codex-cx-tx1-finish-20261110')
 s=s.replace('NLI_exports_20261109','NLI_exports_20261110')
 (E/('NLI_'+name)).write_text(s)
# Unchanged C inputs for existing walker and memory limit, copied once with hashes.
(E/'NLI_native').mkdir(exist_ok=True)
pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 shutil.copyfile(P/'NLC_native'/n,E/'NLI_native'/n);pins[n]=hashlib.sha256((E/'NLI_native'/n).read_bytes()).hexdigest()
(E/'NLI_AUDIT_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(a['roots']),groups=len(a['groups']),expected_import_conflicts=0)))

(E/'NLI_PATHS.json').write_text(json.dumps(json.loads((E/'NLI_ENV.json').read_text())['LEAN_PATH'].split(':')))
priors={tag:json.loads(lzma.decompress((base/(tag+'_CLOSURE_PINS.json.xz')).read_bytes())) for tag,base in [('NLG',W),('NLC',P)]}
(E/'NLI_PREDECESSORS.json.xz').write_bytes(lzma.compress(json.dumps(priors).encode()))
