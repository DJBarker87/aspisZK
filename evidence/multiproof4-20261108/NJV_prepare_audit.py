from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'multiproof3-20261108';Q=E.parent/'ledger15-20261108'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
last={}
for line in (E/'NJV_ATTEMPTS.jsonl').read_text().splitlines():
 x=json.loads(line)
 if x['kind']=='lean':last[x['module']]=x
modules=[];roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for p in sorted((E/'NJV_lean').glob('NJV_*.lean')):
 if p.stem in ['NJV_COMBINED_IMPORT','NJV_Driver','NJV_ProofDriver']:continue
 a=last.get(p.stem);assert a and a['exit_status']==0,p.stem
 archived=E/a['attempt']/'sources'/'NJV_lean'/p.name;assert archived.read_bytes()==p.read_bytes(),p.stem
 modules.append(p.stem);namespace=re.findall(r'^namespace (\S+)',p.read_text(),re.M)[0]
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(n if n.startswith(namespace+'.') else namespace+'.'+n)
 pins[p.stem]=dict(source_sha256=sha(p),successful_attempt=a['attempt'])
imports=['NJO_COMBINED_IMPORT','NJP_COMBINED_IMPORT']+modules
s=''.join('import '+m+'\n' for m in imports)+'\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'
s+='\n'.join('#print '+n+'\n#print axioms '+n for n in ['NJV_TX2.TX2_093','NJV_TX2.abort','NJV_TX1.TX1_127','NJV_TX1.abort'])+'\n'
(E/'NJV_COMBINED_IMPORT.lean').write_text(s);(E/'NJV_lean/NJV_COMBINED_IMPORT.lean').write_text(s)
expected={}
for p in [Q/'NJO_EXPECTED_IMPORTS.jsonl',P/'NJP_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x['imports']
  expected[x['module']]=x['imports']
for m in modules:expected[m]=['Init']+re.findall(r'^import (\S+)',(E/'NJV_lean'/f'{m}.lean').read_text(),re.M)
expected['NJV_COMBINED_IMPORT']=['Init']+imports
(E/'NJV_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
(E/'NJV_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=2)+'\n')
(E/'NJV_AUDIT_MODULES.json').write_text(json.dumps([['NJV_COMBINED_IMPORT']],indent=2)+'\n')
(E/'NJV_PROOF_INVENTORY.json').write_text(json.dumps(dict(modules=pins,roots=roots,target_established=False),indent=2)+'\n')
(E/'NJV_native').mkdir(exist_ok=True)
adapt=[]
for name in ['NJP_Driver','NJP_ProofDriver']:
 old=P/'NJP_lean'/(name+'.lean');new=E/'NJV_lean'/(name.replace('NJP','NJV')+'.lean')
 t=old.read_text().replace('NJP','NJV').replace('namespace NER','namespace NJV_Inspector').replace('end NER','end NJV_Inspector').replace('NER.','NJV_Inspector.')
 new.write_text(t);adapt.append(dict(source=str(old),sha256=sha(old),destination=str(new),destination_sha256=sha(new),changes='owned module/manifest/output/inspector namespace names only; audit algorithm unchanged'))
for n in ['NFA_WALKER','NFA_MemoryLimit']:
 old=P/'NJP_native'/('NJP_'+n+'.c');new=E/'NJV_native'/('NJV_'+n+'.c');new.write_bytes(old.read_bytes());adapt.append(dict(source=str(old),sha256=sha(old),destination=str(new),destination_sha256=sha(new),changes='byte-identical C helper'))
(E/'NJV_AUDIT_ADAPTATIONS.json').write_text(json.dumps(adapt,indent=2)+'\n')
files=['NJV_lean/NJV_ProofDriver.lean','NJV_native/NJV_NFA_WALKER.c','NJV_native/NJV_NFA_MemoryLimit.c','NJV_AUDIT_ROOTS.json','NJV_AUDIT_MODULES.json','NJV_EXPECTED_IMPORTS.jsonl']
for old,num,kind in [('020',43,'lean'),('021',44,'lean'),('022',45,'link'),('023',46,'link'),('024',47,'audit'),('025',48,'lean'),('026',49,'audit'),('027',50,'audit')]:
 c=json.loads((P/f'NJP_L{old}.json').read_text());c['attempt']=f'NJV_L{num:03d}';c['module']=c['module'].replace('NJP','NJV');c['command']=[v.replace('NJP','NJV') for v in c['command']];c['env']=json.loads((E/'NJV_ENV.json').read_text());c['sources']=[v.replace('NJP','NJV') for v in c['sources']];c['upload']=[v.replace('NJP','NJV') for v in c.get('upload',[])];c['collect']=[v.replace('NJP','NJV') for v in c.get('collect',[])];c['expected_time']='Focused audit driver elaboration/link, fixtures, then ONE complete combined import/scan/raw ax2 gate; optimized audit binary, no arithmetic gate'
 if num in [43,44]:c['collect']=[f'NJV_native/{c["module"]}.c']
 if num in [45,46]:c['sources'].append(f'NJV_native/{c["module"]}.c')
 if num==50:c['collect']=[]
 (E/(c['attempt']+'.json')).write_text(json.dumps(c,indent=2)+'\n')
print(f'NJV audit prepared: {len(modules)} proof modules, {len(roots)} roots, NJO+NJP+deployed; algorithm unchanged')
