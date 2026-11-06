"""Own name/schema adaptation of the unchanged predecessor audit algorithms."""
from pathlib import Path
import json,re,hashlib,lzma,sys
sys.dont_write_bytecode=True
import NKB_resolve
E=Path(__file__).resolve().parent;P=E.parent/'multiproof4-20261108';Q=E.parent/'ledger16-20261108';R=E.parent/'batch-merkle-20261108'
def read(p):
 if p.is_relative_to(E):return NKB_resolve.read(str(p.relative_to(E)))
 if p.is_file():return p.read_bytes()
 if p.with_name(p.name+'.xz').is_file():
  data=lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert hashlib.sha256(data).hexdigest()==p.with_name(p.name+'.sha256').read_text().strip();return data
 raise FileNotFoundError(p)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['NKB_Rejection','NKB_IndexFold','NKB_CallerDomain','NKB_CallerPrefix','NKB_DedupCut','NKB_LeafChain','NKB_PaddingFrame','NKB_PaddingPredicate','NKB_ScanWindows','NKB_SortProducer','NKB_StrictCount','NKB_StrictLeaves','NKB_DomainFinding','NKB_ProducerChain','NKB_AnyModel','NKB_KeyStream','NKB_ParseCut']
last={}
for line in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines():
 x=json.loads(line)
 if x['kind']=='lean':last[x['module']]=x
roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for m in modules:
 p=E/'NKB_lean'/(m+'.lean');a=last[m];assert a['exit_status']==0,m
 archived=E/a['attempt']/'sources'/'NKB_lean'/p.name;assert read(archived)==p.read_bytes(),m
 ns=re.findall(r'^namespace (\S+)',p.read_text(),re.M)[0]
 for name in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(name if name.startswith(ns+'.') else ns+'.'+name)
 pins[m]=dict(source_sha256=sha(p),successful_attempt=a['attempt'])
imports=['NJW_COMBINED_IMPORT','NJS_COMBINED_IMPORT','NJV_COMBINED_IMPORT']+modules
s=''.join('import '+m+'\n' for m in imports)+'\nset_option pp.proofs false\n'
s+=''.join('#print '+root+'\n#print axioms '+root+'\n' for root in roots)
(E/'NKB_COMBINED_IMPORT.lean').write_text(s);(E/'NKB_lean/NKB_COMBINED_IMPORT.lean').write_text(s)
expected={}
for d,prefix in [(Q,'NJW'),(R,'NJS'),(P,'NJV')]:
 for line in read(d/(prefix+'_EXPECTED_IMPORTS.jsonl')).decode().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x['imports'],x['module']
  expected[x['module']]=x['imports']
for m in modules:expected[m]=['Init']+re.findall(r'^import (\S+)',(E/'NKB_lean'/(m+'.lean')).read_text(),re.M)
expected['NKB_COMBINED_IMPORT']=['Init']+imports
(E/'NKB_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
(E/'NKB_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=2)+'\n')
(E/'NKB_AUDIT_MODULES.json').write_text(json.dumps([['NKB_COMBINED_IMPORT']],indent=2)+'\n')
(E/'NKB_PROOF_INVENTORY.json').write_text(json.dumps(dict(modules=pins,roots=roots,target_established=False,closed_rows=0),indent=2)+'\n')
(E/'NKB_native').mkdir(exist_ok=True);adapt=[]
for name in ['NJV_Driver','NJV_ProofDriver']:
 old=P/'NJV_lean'/(name+'.lean');new=E/'NKB_lean'/(name.replace('NJV','NKB')+'.lean');new.write_text(old.read_text().replace('NJV','NKB'))
 adapt.append(dict(source=str(old),sha256=sha(old),destination=str(new),destination_sha256=sha(new),changes='owned names/manifest/output/inspector namespace only; audit algorithm unchanged'))
for name in ['NFA_WALKER','NFA_MemoryLimit']:
 old=P/'NJV_native'/('NJV_'+name+'.c');new=E/'NKB_native'/('NKB_'+name+'.c');new.write_bytes(read(old));adapt.append(dict(source=str(old),sha256=hashlib.sha256(read(old)).hexdigest(),destination=str(new),destination_sha256=sha(new),changes='byte-identical C helper'))
(E/'NKB_AUDIT_ADAPTATIONS.json').write_text(json.dumps(adapt,indent=2)+'\n')
for old,num in [(60,40),(61,41),(62,42),(63,43),(64,44),(65,45),(66,46),(67,47)]:
 c=json.loads((P/f'NJV_L{old:03d}.json').read_text());c['attempt']=f'NKB_L{num:03d}';c['module']=c['module'].replace('NJV','NKB');c['command']=[v.replace('NJV','NKB') for v in c['command']];c['env']=json.loads((E/'NKB_ENV.json').read_text())
 for key in ['sources','upload','collect']:c[key]=[v.replace('NJV','NKB') for v in c.get(key,[])]
 c['expected_time']='Focused audit-driver elaboration/link or unchanged fidelity fixtures; final NJW+NJS+NJV+headline combined gate, optimized audit executable'
 (E/(c['attempt']+'.json')).write_text(json.dumps(c,indent=2)+'\n')
print('NKB audit prepared: '+str(len(modules))+' support modules, '+str(len(roots))+' roots; no parent row claimed')
