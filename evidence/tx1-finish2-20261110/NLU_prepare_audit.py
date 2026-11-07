from pathlib import Path
import json,re,lzma,hashlib,shutil
E=Path(__file__).resolve().parent
bases=[('NLO',E.parent/'ledger22-20261110'),('NLI',E.parent/'tx1-finish-20261110'),('NLC',E.parent/'tx1-driver2-20261109'),('NLH',E.parent/'terminal6-20261110')]
latest={}
for p in E.glob('NLU_L*/receipt.json'):
 x=json.loads(p.read_text());m=x.get('module','');src=E/'NLU_generated'/(m+'.lean');snap=p.parent/'sources/NLU_generated'/(m+'.lean')
 if x.get('kind')=='lean' and x['exit_status']==0 and src.exists() and snap.exists() and src.read_bytes()==snap.read_bytes() and not m.startswith('NLU_Inspect'):
  latest[m]=(x,p)
assert 'NLU_SourceProjection' in latest
roots=[]
for m,(x,p) in latest.items():
 roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(p.parent/'stdout.log').read_text())
roots=sorted(set(roots));mods=sorted(latest)
text=''.join('import '+tag+'_COMBINED_IMPORT\n' for tag,_ in bases)+''.join('import '+m+'\n' for m in mods)+'\n-- Support gate only; no136 native root or ledger credit is implied.\n'
for n in ['AspisR1.RPx_Deployed.deployed']+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
(E/'NLU_generated/NLU_COMBINED_IMPORT.lean').write_text(text);(E/'NLU_COMBINED_IMPORT.lean').write_text(text)
allroots=[];expected={};conflicts=[]
for tag,base in bases:
 a=json.loads((base/(tag+'_AUDIT_ROOTS.json')).read_text());allroots+=a['roots']
 for line in (base/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(line);old=expected.get(x['module'])
  if old and set(old['imports'])!=set(x['imports']):conflicts.append(dict(module=x['module'],before=old,after=x))
  expected[x['module']]=x
assert not conflicts,conflicts
allroots=list(dict.fromkeys(allroots+roots));groups=[allroots[i::31] for i in range(31)]
(E/'NLU_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups)))
(E/'NLU_AUDIT_MODULES.json').write_text(json.dumps([['NLU_COMBINED_IMPORT'] for _ in groups]))
for m in mods+['NLU_COMBINED_IMPORT']:
 s=(E/'NLU_generated'/(m+'.lean')).read_text();imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',s,re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NLU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in expected.values()))
for name in ['Driver','ProofDriver']:
 s=(E.parent/'tx1-finish-20261110/NLI_generated'/('NLI_'+name+'.lean')).read_text().replace('NLI','NLU')
 (E/'NLU_generated'/('NLU_'+name+'.lean')).write_text(s)
for name in ['audit_batch.py','audit_config.py','pin.py']:
 s=(E.parent/'tx1-finish-20261110'/('NLI_'+name)).read_text().replace('NLI','NLU').replace('codex-cx-tx1-finish-20261110','codex-cx-tx1-finish2-20261110')
 (E/('NLU_'+name)).write_text(s)
p=E/'NLU_audit_batch.py';s=p.read_text().replace("exec(compile((B/'NLU_pin.py').read_text(),'NLU_pin.py','exec'));sys.exit(0)","exec(compile((B/'NLU_pin.py').read_text(),'NLU_pin.py','exec'));exec(compile((B/'NLU_preflight.py').read_text(),'NLU_preflight.py','exec'));sys.exit(0)");p.write_text(s)
p=E/'NLU_audit_config.py';s=p.read_text().replace("['NLU_pin.py','NLU_PREDECESSORS.json.xz']","['NLU_pin.py','NLU_PREDECESSORS.json.xz','NLU_preflight.py']").replace("'NLU_EXPORT.json']","'NLU_EXPORT.json','NLU_PREFLIGHT.json']");p.write_text(s)
(E/'NLU_native').mkdir(exist_ok=True);cpins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=E.parent/'tx1-finish-20261110/NLI_native'/n;shutil.copyfile(src,E/'NLU_native'/n);cpins[n]=hashlib.sha256(src.read_bytes()).hexdigest()
(E/'NLU_AUDIT_INPUT_PINS.json').write_text(json.dumps(cpins,indent=1))
(E/'NLU_PATHS.json').write_text(json.dumps(json.loads((E/'NLU_ENV.json').read_text())['LEAN_PATH'].split(':')))
priors={tag:json.loads(lzma.decompress((base/(tag+'_CLOSURE_PINS.json.xz')).read_bytes())) for tag,base in bases if (base/(tag+'_CLOSURE_PINS.json.xz')).exists()}
blob=json.dumps(priors).encode();(E/'NLU_PREDECESSORS.json.xz').write_bytes(lzma.compress(blob));(E/'NLU_PREDECESSORS.json.sha256').write_text(hashlib.sha256(blob).hexdigest()+'\n')
(E/'NLU_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,row_roots=[],status='SUPPORT_ONLY',groups=31),indent=1))
print(json.dumps(dict(modules=len(mods),own_roots=len(roots),required_roots=len(allroots),groups=len(groups),expected_import_conflicts=0)))
