"""Task-local wrapper around the existing reservation scanner and run2.py.
Caller must first run turn.sh over its own standalone SSH command.
Only the SPEC host directory is written. No cache rebuild or cap changes.
"""
import hashlib,json,lzma,os,pathlib,subprocess,sys,time
P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107')
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-20261107')
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
a=int(sys.argv[1]);module=sys.argv[2];rev=sys.argv[3]
cohort=sys.argv[4] if len(sys.argv)>4 else 'base'
assert cohort in ['base','stx']
assert cohort=='stx'
O=P/'objects-stx';O.mkdir(exist_ok=True)
J=P/('J-stx.json' if cohort=='stx' else 'J.json')
if cohort=='stx': B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-stx-20261104')
assert 49920<=a<=49999
src=P/'sources'/f'{module}.lean'; ev=P/'evidence'
assert not (O/f'{module}.olean').exists()
receipt=ev/f'receipt-{a}.json'
assert not receipt.exists()
srchash=sha(src)
for f in ev.glob('receipt-*.json'):
 old=json.loads(f.read_text())
 assert not(old.get('source_sha256')==srchash and old.get('exit') not in [0,78] and old.get('class')=='elaboration'), 'unchanged failed source'
# Reuse the accepted D937 library cohort read-only, checked against base receipts.
auth=json.loads(lzma.decompress((P/('STX_OBJECT_AUTHORITY.json.xz' if cohort=='stx' else 'BASE_OBJECT_AUTHORITY.json.xz')).read_bytes()))['modules']
checks={}
for file in ev.glob('receipt-*.json'):
 old=json.loads(file.read_text())
 if old.get('accepted') and old.get('cohort','base')==cohort and not old.get('runtime_audit'):
  object_path=O/(old['target']+'.olean')
  assert sha(object_path)==old['object_sha256'], 'own object changed'
  assert sha(P/'sources'/(old['target']+'.lean'))==old['source_sha256'], 'own source changed'
  checks[old['target']]={'path':str(object_path),'sha256':old['object_sha256']}
for m,x in auth.items():
 path=pathlib.Path(x['path'])
 actual=sha(path)
 assert actual==x['sha256'], f'authority mismatch {m}: {path}'
 checks[m]={'path':str(path),'sha256':actual}
(ev/f'resolution-{a}.json.xz').write_bytes(lzma.compress(json.dumps(checks).encode()))
env=json.loads((B/'J.json').read_text())
env['LEAN_PATH']=str(O)+':'+env['LEAN_PATH']
J.write_text(json.dumps(env))
rec={'cohort':cohort,'attempt':a,'target':module,'source_revision':rev,'source_sha256':srchash,'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000},'resolution_modules':len(checks)}
scanner='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
with (ev/f'admission-{a}.log').open('w') as out:
 admission=subprocess.run(['python3',scanner,str(ev/f'admission-{a}.json')],stdout=out,stderr=subprocess.STDOUT)
allowed=json.loads((ev/f'admission-{a}.json').read_text()).get('allowed')
if admission.returncode!=0 or allowed is not True:
 rec.update(exit=admission.returncode,accepted=False,**{'class':'admission'})
 receipt.write_text(json.dumps(rec,indent=2));print(json.dumps(rec));sys.exit(admission.returncode or 78)
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-lib-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(ev/f'time-{a}.log'),'timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(J),str(O),str(P/'sources'),str(O/f'{module}.olean'),str(src),'7000']
start=time.time()
with (ev/f'out-{a}.log').open('w') as out:
 r=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT,cwd=P)
rec.update(command=cmd,exit=r.returncode,wall_seconds=time.time()-start,accepted=r.returncode==0,**{'class':'elaboration'})
log=(ev/f'out-{a}.log').read_text(); timing=(ev/f'time-{a}.log').read_text()
rec['axioms_summary_based']=[l for l in log.splitlines() if 'axioms' in l]
for line in timing.splitlines():
 for key,field in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
  if key in line:rec[field]=line.split(key)[1].strip()
if r.returncode==0:rec['object_sha256']=sha(O/f'{module}.olean')
receipt.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));print(log)
sys.exit(r.returncode)
