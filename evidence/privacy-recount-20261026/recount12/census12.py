"""Inventory receipts from immutable pins. Does not execute any receipt command."""
import subprocess,json,re,hashlib,lzma
from pathlib import Path
P=Path(__file__).resolve().parent;pins=json.loads((P/'pins.json').read_text()); revs=pins['revisions']
def git(*a):return subprocess.check_output(['git',*a])
# One copy per blob, including failed and superseded attempts; no success inferred from process exit.
objects={};entries=[]
for ref,rev in revs.items():
 lines=git('ls-tree','-r',rev).decode().splitlines()
 bypath={a.split('\t',1)[1]:a.split()[2] for a in lines}
 paths=[p for p in bypath if re.search(r'/K9\d{4}/(?:receipt/)?receipt.json$',p) and p.startswith('evidence/pv-')]
 for p in paths:
  blob=bypath[p]
  if blob not in objects:objects[blob]=git('cat-file','blob',blob).decode()
  try:r=json.loads(objects[blob])
  except ValueError:continue
  command=r.get('target',r.get('command',r.get('cmd',[])));command=' '.join(map(str,command)) if isinstance(command,list) else str(command)
  if 'kani' not in command.lower():continue
  root=p.rsplit('/receipt/receipt.json',1)[0] if p.endswith('/receipt/receipt.json') else p.rsplit('/',1)[0]
  files={q:bypath[q] for q in bypath if q.startswith(root+'/') and any(t in q for t in ['output.log','stdout.log','trace','source-sha','command.json','inputs.json','admission','reservation','barrier']) and not any(t in q for t in ['metadata','symbols','symtab'])}
  for q,b in files.items():
   if b not in objects:
    data=git('cat-file','blob',b)
    if len(data)<2000000:
     try:objects[b]=data.decode()
     except UnicodeDecodeError:pass
  entries.append({'ref':ref,'revision':rev,'id':re.search(r'K9\d{4}',p).group(),'path':p,'receipt_blob':blob,'command':command,'receipt':r,'files':files})
(P/'kani-receipt-census12.json').write_text(json.dumps(entries,indent=1)+'\n')
(P/'kani-receipt-inputs12.json.xz').write_bytes(lzma.compress(json.dumps(objects).encode()))
print('receipt references',len(entries),'unique ids',len(set(e['id'] for e in entries)),'objects',len(objects))
for e in entries:
 if e['ref'] in ['stx','stxb','b3p6','evhB'] and int(e['id'][1:])>=92600:
  out='\n'.join(objects.get(b,'') for q,b in e['files'].items() if q.endswith(('output.log','stdout.log')))
  positives=re.findall(r'Checking harness (.*?)\.\.\.[\s\S]*?VERIFICATION:- (SUCCESSFUL|FAILED)',out)
  print(e['ref'],e['id'],positives)
