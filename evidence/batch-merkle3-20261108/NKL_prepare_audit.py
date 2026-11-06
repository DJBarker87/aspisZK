"""Owned paths/manifests only; predecessor audit algorithms are unchanged."""
from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent;P=E.parent/'batch-merkle2-20261108';Q=E.parent/'ledger18-20261108'
def read(p):
 if p.is_file():return p.read_bytes()
 data=lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
 assert hashlib.sha256(data).hexdigest()==p.with_name(p.name+'.sha256').read_text().strip()
 return data
sha=lambda b:hashlib.sha256(b).hexdigest()
history=[json.loads(s) for s in (E/'NKL_ATTEMPTS.jsonl').read_text().splitlines()];last={}
for a in history:
 if a['kind']=='lean' and a['exit_status']==0:last[a['module']]=a
modules=[];roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for p in sorted(E.glob('NKL_*.lean')):
 m=p.stem
 if m=='NKL_COMBINED_IMPORT':continue
 a=last[m];assert a['source_hashes'][p.name]==sha(p.read_bytes()),m
 modules.append(m);ns=re.findall(r'^namespace (\S+)',p.read_text(),re.M)[0]
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(n if n.startswith(ns+'.') else ns+'.'+n)
 pins[m]=dict(source_sha256=sha(p.read_bytes()),successful_attempt=a['attempt'])
imports=['NKH_COMBINED_IMPORT']+modules
s=''.join('import '+m+'\n' for m in imports)+'\nset_option pp.proofs false\n'
s+=''.join('#print '+r+'\n#print axioms '+r+'\n' for r in roots)
(E/'NKL_COMBINED_IMPORT.lean').write_text(s)
expected={}
for d,n in [(Q,'NKH'),(P,'NKB')]:
 for line in read(d/(n+'_EXPECTED_IMPORTS.jsonl')).decode().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x['imports'],x['module']
  expected[x['module']]=x['imports']
for m in modules:expected[m]=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)
expected['NKL_COMBINED_IMPORT']=['Init']+imports
(E/'NKL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
(E/'NKL_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=2)+'\n')
(E/'NKL_AUDIT_MODULES.json').write_text(json.dumps([['NKL_COMBINED_IMPORT']])+'\n')
(E/'NKL_PROOF_INVENTORY.json').write_text(json.dumps(dict(modules=pins,roots=roots,target_established=False),indent=2)+'\n')
(E/'NKL_lean').mkdir(exist_ok=True);(E/'NKL_native').mkdir(exist_ok=True);adapt=[]
for name in ['Driver','ProofDriver']:
 old=P/'NKB_lean'/('NKB_'+name+'.lean');new=E/'NKL_lean'/('NKL_'+name+'.lean');new.write_text(old.read_text().replace('NKB','NKL'))
 adapt.append(dict(source=str(old),sha256=sha(old.read_bytes()),destination=str(new),destination_sha256=sha(new.read_bytes()),change='owned names/paths only'))
for name in ['NFA_WALKER','NFA_MemoryLimit']:
 old=P/'NKB_native'/('NKB_'+name+'.c');new=E/'NKL_native'/('NKL_'+name+'.c');new.write_bytes(read(old));adapt.append(dict(source=str(old),sha256=sha(read(old)),destination=str(new),change='byte identical'))
old=P/'NKB_audit2_binary.py';new=E/'NKL_audit_binary.py';new.write_text(old.read_text().replace('NKB','NKL'));adapt.append(dict(source=str(old),sha256=sha(old.read_bytes()),destination=str(new),change='owned binary and output paths only'))
(E/'NKL_AUDIT_ADAPTATIONS.json').write_text(json.dumps(adapt,indent=2)+'\n')
env=json.loads((E/'NKL_ENV.json').read_text())
for old,num in [(40,64),(41,65),(42,66),(43,67),(100,90),(101,91),(102,92)]:
 c=json.loads((P/f'NKB_L{old:03}.json').read_text());c['attempt']=f'NKL_L{num:03}';c['module']=c['module'].replace('NKB','NKL');c['env']=env
 for k in ['command','sources','upload','collect']:
  c[k]=[v.replace('NKB','NKL').replace('NKL_audit2_binary','NKL_audit_binary').replace('NKL_lean/NKL_COMBINED_IMPORT','NKL_COMBINED_IMPORT') for v in c.get(k,[])]
 c['expected_time']='Focused audit driver compile/optimized link; final combined audit on unchanged NEP/NFX/ax2 walker, exact headline and all NKL theorem roots'
 (E/(c['attempt']+'.json')).write_text(json.dumps(c,indent=2)+'\n')
print(f'NKL audit prepared: {len(modules)} modules, {len(roots)} roots; target not established')
