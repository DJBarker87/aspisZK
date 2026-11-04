#!/usr/bin/env python3
"""Mechanically retain file/body/model identity for structured own-1 receipts.
This validates the source association, not the semantic sufficiency of a proof.
"""
import hashlib,json,subprocess
from pathlib import Path
import PV_MF_check as C
D=Path(__file__).resolve().parent;files=C.load('FILES.json');evidence=C.load('EVIDENCE.json');sha=lambda b:hashlib.sha256(b).hexdigest()
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);cache={}
def blob(h):
 if h not in cache:
  proc.stdin.write((h+'\n').encode());proc.stdin.flush();a=proc.stdout.readline().split();b=proc.stdout.read(int(a[2]));proc.stdout.read(1);cache[h]=b
 return cache[h]
out=[]
for e in evidence:
 p=e['path']
 if not p.endswith('.json') or not any(k in p.lower() for k in ['binding','structural','association']):continue
 try:j=json.loads(blob(files[p]['git_blob']))
 except ValueError:continue
 def walk(x,loc=''):
  if isinstance(x,list):
   for i,y in enumerate(x):walk(y,loc+'/'+str(i))
  elif isinstance(x,dict):
   r=x.get('rust');lp=x.get('lean_path')
   if isinstance(r,dict) and lp in files and r.get('path') in files and r.get('file_sha256') and 'text' in r and 'first_line' in r and 'last_line' in r:
    rp=r['path'];source=blob(files[rp]['git_blob']);span=b''.join(source.splitlines(keepends=True)[r['first_line']-1:r['last_line']]);model=blob(files[lp]['git_blob']);txt=r['text'].encode()
    checks={'file':sha(source)==r['file_sha256'],'recorded_span_digest':sha(txt)==r.get('sha256'),'current_source_span':span==txt,'model':sha(model)==x.get('lean_sha256')}
    out.append({'receipt':p,'pointer':loc,'function':x.get('name'),'source':{'path':rp,**files[rp]},'span':{'first_line':r['first_line'],'last_line':r['last_line'],'sha256':r.get('sha256')},'model':{'path':lp,**files[lp]},'checks':checks,'identity_status':'IDENTICAL' if all(checks.values()) else 'STALE_OR_SPAN_MISMATCH','evidence_class':'own-1 structural (inherited partial source binding; semantic law not re-audited)','recorded_scope':j.get('classification') if isinstance(j,dict) else None,'association':x.get('association'),'mutable_restore_check':x.get('mutable_restore_check'),'whole_row_credit':False})
   for k,y in x.items():
    if isinstance(y,(dict,list)):walk(y,loc+'/'+k)
 walk(j)
(D/'SOURCE-BINDINGS.json').write_text(json.dumps(out,indent=1)+'\n');print('structured source spans',len(out),'identical',sum(r['identity_status']=='IDENTICAL' for r in out))
