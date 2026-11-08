"""One strict audit attempt, one isolated W3 cohort.
No combined-cohort claim; unchanged importAll/private NEP collector in each.
Run turn.sh separately before invoking this task-local launch wrapper.
"""
import hashlib,json,os,pathlib,subprocess,sys,time,lzma
P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107');E=P/'evidence'
def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def checked():
 for rfile in E.glob('receipt-*.json'):
  r=json.loads(rfile.read_text())
  if r.get('accepted') and r.get('object_sha256'):
   root=P/('objects-'+r['cohort'] if r.get('cohort','base')!='base' else 'objects')
   assert sha(root/(r['target']+'.olean'))==r['object_sha256']
   assert sha(P/'sources'/(r['target']+'.lean'))==r['source_sha256']
 for c in ['W3_COMPAT','W4','LANEA']:
  auth=json.loads(lzma.decompress((P/(c+'_OBJECT_AUTHORITY.json.xz')).read_bytes()))['modules']
  for m,v in auth.items():assert sha(v['path'])==v['sha256'],m
if len(sys.argv)>1 and sys.argv[1]=='--inside':
 failures=[]
 for cohort,driver,env in [('w3','Session8','J-w3.json')]:
  cmd=['python3',str(P/'run-thread-audit.py'),str(P/env),str(P/'sources'/('PV_LIB_SPEC_RawAudit'+driver+'.lean'))]
  with (E/('out-49798-'+cohort+'.log')).open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=P)
  print(json.dumps({'cohort':cohort,'exit':r.returncode,'command':cmd}),flush=True)
  failures.append(r.returncode)
 sys.exit(max(failures))
assert sys.argv[1]=='49798'
assert not (E/'receipt-49798.json').exists()
checked()
inputs = {str(p):sha(p) for p in [P/'sources'/'PV_LIB_SPEC_RawAuditSession8.lean',P/'host_audit_s8.py',P/'run-thread-audit.py']}
(E/'inputs-49798.json').write_text(json.dumps(inputs,indent=2))
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
with (E/'admission-49798.log').open('w') as f:r=subprocess.run(['python3',scanner,str(E/'admission-49798.json')],stdout=f,stderr=subprocess.STDOUT)
allowed=json.loads((E/'admission-49798.json').read_text()).get('allowed')
if r.returncode!=0 or allowed is not True:
 (E/'receipt-49798.json').write_text(json.dumps({'attempt':49798,'exit':r.returncode,'accepted':False,'class':'admission','epoch':time.time()}));sys.exit(r.returncode or 78)
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-lib-spec-49798','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(E/'time-49798.log'),'timeout','600','python3',str(P/'host_audit_s8.py'),'--inside']
with (E/'out-49798.log').open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=P)
rec={'attempt':49798,'target':'SPEC session8 new logical roots, isolated W3 cohort','source_revision':sys.argv[2],'exit':r.returncode,'accepted':r.returncode==0,'command':cmd,'cohort_combination_claimed':False}
for line in (E/'time-49798.log').read_text().splitlines():
 for key,field in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
  if key in line:rec[field]=line.split(key)[1].strip()
rec['axioms_summary_based']=[]
for c in ['w3']:
 log=E/('out-49798-'+c+'.log')
 if log.exists():rec['axioms_summary_based'] += [l for l in log.read_text().splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
(E/'receipt-49798.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items() if k!='axioms_summary_based'}))
sys.exit(r.returncode)
