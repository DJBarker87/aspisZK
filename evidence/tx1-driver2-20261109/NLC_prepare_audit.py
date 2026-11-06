from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'tx1-driver-20261108';W=E.parent/'ledger20-20261109'
latest={}
for f in E.glob('NLC_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(f.read_text());m=r.get('module')
 if r['kind']!='lean' or r['exit_status'] or not m or m=='NLC_Inspect':continue
 src=E/'NLC_generated'/(m+'.lean');tested=f.parent/'sources/NLC_generated'/(m+'.lean')
 if src.exists() and tested.exists() and src.read_bytes()==tested.read_bytes():latest[m]=(r,f)
mods=sorted(latest);roots=[]
for m,(r,f) in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
assert 'NLC_InitializedInvocation' in mods and 'NLC_MapCut' in mods
text='import NKW_COMBINED_IMPORT\nimport NKQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n-- No row root or native parent fold; source interpreter and local windows only.\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
(E/'NLC_generated/NLC_COMBINED_IMPORT.lean').write_text(text);(E/'NLC_COMBINED_IMPORT.lean').write_text(text)
(E/'NLC_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,unproved_goal='AspisR1.NLC_Goals.FinishSourceEquality',row_roots=[]),indent=2))
a=json.loads((W/'NKW_AUDIT_ROOTS.json').read_text());all_old=set(a['roots'])
extra=[x for x in json.loads((P/'NKQ_AUDIT_ROOTS.json').read_text())['roots']+roots if x not in all_old];extra=sorted(set(extra));a['groups'].append(extra);a['roots']=a['roots']+extra
(E/'NLC_AUDIT_ROOTS.json').write_text(json.dumps(a));(E/'NLC_AUDIT_MODULES.json').write_text(json.dumps([['NLC_COMBINED_IMPORT'] for _ in a['groups']]))
expected={};conflicts=[]
for path in [W/'NKW_EXPECTED_IMPORTS.jsonl',P/'NKQ_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLC_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLC_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NLC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(P/'NKQ_generated'/('NKQ_'+name+'.lean')).read_text().replace('NKQ_','NLC_')
 (E/'NLC_generated'/('NLC_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(P/('NKQ_'+name)).read_text().replace('NKQ','NLC').replace('codex-cx-tx1-driver-20261108','codex-cx-tx1-driver2-20261109')
 (E/('NLC_'+name)).write_text(s)
# Unchanged C inputs for existing walker and memory limit, copied once with hashes.
(E/'NLC_native').mkdir(exist_ok=True)
pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 shutil.copyfile(P/'NKQ_native'/n,E/'NLC_native'/n);pins[n]=hashlib.sha256((E/'NLC_native'/n).read_bytes()).hexdigest()
(E/'NLC_AUDIT_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(a['roots']),groups=len(a['groups']),expected_import_conflicts=0)))
