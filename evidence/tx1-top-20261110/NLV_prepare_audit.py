from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'tx1-prepare-20261110';W=E.parent/'ledger23-20261110';C=E.parent/'tx1-driver2-20261109';N=E.parent/'batch-merkle6-20261110'
latest={}
for f in sorted(E.glob('NLV_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());m=r.get('module')
 if r['kind']!='lean' or r['exit_status'] or not m or m in ['NLV_Inspect','NLV_Driver','NLV_ProofDriver','NLV_COMBINED_IMPORT']:continue
 src=E/'NLV_generated'/(m+'.lean');tested=f.parent/'sources/NLV_generated'/(m+'.lean')
 if src.exists() and tested.exists() and src.read_bytes()==tested.read_bytes():latest[m]=(r,f)
mods=sorted(latest);roots=[]
for m,(r,f) in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
roots=sorted(set(roots));headline='AspisR1.RPx_Deployed.deployed'
assert all(m in mods for m in ['NLV_InitialFold','NLV_QueryCanonical','NLV_CutFold','NLV_Deployed'])
text='import NLS_COMBINED_IMPORT\nimport NLJ_COMBINED_IMPORT\nimport NLC_COMBINED_IMPORT\nimport NLN_TX1_081\n'+''.join('import '+m+'\n' for m in mods)+'\n-- No CLOSED094 root; parameterized support only.\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
text+='\nset_option pp.proofs false\n'
for n in ['AspisR1.NLV_Tree.from_cuts','AspisR1.NLV.source_cuts']:text+='#print '+n+'\n'
(E/'NLV_generated/NLV_COMBINED_IMPORT.lean').write_text(text);(E/'NLV_COMBINED_IMPORT.lean').write_text(text)
(E/'NLV_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,selected_receipts={m:str(f.relative_to(E)) for m,(r,f)in latest.items()},row_roots=[]),indent=2))
allroots=sorted(set(json.loads((W/'NLS_AUDIT_ROOTS.json').read_text())['roots']+json.loads((P/'NLJ_AUDIT_ROOTS.json').read_text())['roots']+json.loads((C/'NLC_AUDIT_ROOTS.json').read_text())['roots']+json.loads((N/'NLN_AUDIT_ROOTS.json').read_text())['roots']+roots))
groups=[allroots[len(allroots)*j//30:len(allroots)*(j+1)//30]for j in range(30)]
(E/'NLV_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups)))
(E/'NLV_AUDIT_MODULES.json').write_text(json.dumps([['NLV_COMBINED_IMPORT']for _ in groups]))
expected={};conflicts=[]
for path in [W/'NLS_EXPECTED_IMPORTS.jsonl',P/'NLJ_EXPECTED_IMPORTS.jsonl',C/'NLC_EXPECTED_IMPORTS.jsonl',N/'NLN_EXPECTED_IMPORTS.jsonl']:
 for line in (path.read_text() if path.exists() else lzma.decompress((path.parent/json.loads(path.with_suffix(path.suffix+'.ref.json').read_text())['owned_input']).read_bytes()).decode()).splitlines():
  x=json.loads(line)
  if x['module']in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NLV_COMBINED_IMPORT']:
 expected[m]=dict(module=m,imports=list(dict.fromkeys(['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NLV_generated'/(m+'.lean')).read_text(),re.M))))
for m in ['NLR_RowSpec087','NLR_RowSpec137']:
 s=(E/('NLV_READONLY_'+m+'.lean.txt')).read_text();expected[m]=dict(module=m,imports=list(dict.fromkeys(['Init']+re.findall(r'^import (?:all )?([\w.]+)',s,re.M))))
(E/'NLV_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(P/'NLJ_generated'/('NLJ_'+name+'.lean')).read_text().replace('NLJ_','NLV_');(E/'NLV_generated'/('NLV_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(P/('NLJ_'+name)).read_text().replace('NLJ','NLV').replace('codex-cx-tx1-prepare-20261110','codex-cx-tx1-top-20261110')
 # Same raw bytes and hash; fast compression prevents post-verdict packaging
 # from consuming the unchanged180s scope. No walker/proof logic change.
 if name in ['audit_batch.py','pin.py']:s=s.replace('lzma.compress(blob)','lzma.compress(blob,preset=0)').replace('lzma.compress(raw)','lzma.compress(raw,preset=0)')
 (E/('NLV_'+name)).write_text(s)
(E/'NLV_native').mkdir(exist_ok=True);pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 shutil.copyfile(P/'NLJ_native'/n,E/'NLV_native'/n);pins[n]=hashlib.sha256((E/'NLV_native'/n).read_bytes()).hexdigest()
(E/'NLV_AUDIT_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
priors={tag:json.loads(lzma.decompress(path.read_bytes()))for tag,path in [('NLS',W/'NLS_CLOSURE_PINS.json.xz'),('NLJ',P/'NLJ_CLOSURE_PINS.json.xz'),('NLC',C/'NLC_CLOSURE_PINS.json.xz')]}
(E/'NLV_PREDECESSORS.json.xz').write_bytes(lzma.compress(json.dumps(priors).encode(),preset=0))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=30,conflicts=0)))
