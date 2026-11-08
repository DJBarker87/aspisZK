"""Run the single end-of-session strict raw audit of changed roots only."""
import json,pathlib,subprocess,shlex,time,sys
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE');H='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107';host='dombarker@100.108.41.90';a=49693
assert not (E/f'turn-{a}.json').exists()
t=time.time();q=subprocess.run(['ssh',host,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'],capture_output=True,text=True)
turn=dict(attempt=a,exit=q.returncode,wall=time.time()-t,stdout=q.stdout,stderr=q.stderr)
(E/f'turn-{a}.json').write_text(json.dumps(turn,indent=2)+'\n');assert q.returncode==0
payload=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),turn=turn)
code=r'''
import pathlib,json,hashlib,lzma,subprocess,sys,time,re,os
x=json.load(sys.stdin);P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107');E=P/'evidence';a=49693
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
pattern=re.compile(r'(^|[-_])49693([-_.]|$)');hits=[]
for job in P.parent.glob('codex-*'):
 for d,dirs,names in os.walk(job/'evidence'):
  for n in names:
   if pattern.search(n) and os.path.isfile(os.path.join(d,n)):hits.append(os.path.join(d,n))
assert not hits,hits
(E/f'id-audit-{a}.json').write_text(json.dumps(dict(attempt=a,hits=hits)))
# Exact pinned import authority and both accepted new artifacts, no rebuild.
checks=json.loads(lzma.decompress((E/'resolution-49942.json.xz').read_bytes()))
for name,v in checks.items():assert sha(v['path'])==v['sha256'],name
for n in [49924,49926,49928,49929,49930,49931,49932,49933,49934,49935,49936,49941,49942]:
 r=json.loads((E/f'receipt-{n}.json').read_text());assert r['accepted']
 assert sha(P/'sources-stx4'/(r['target']+'.lean'))==r['source_sha256']
 assert sha(P/'objects-stx4'/(r['target']+'.olean'))==r['object_sha256']
scanner='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
with (E/f'admission-{a}.log').open('w') as out:r=subprocess.run(['python3',scanner,str(E/f'admission-{a}.json')],stdout=out,stderr=subprocess.STDOUT)
admission=json.loads((E/f'admission-{a}.json').read_text())
assert r.returncode==0 and admission['allowed'] is True,admission
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-lib-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(E/f'time-{a}.log'),'timeout','600','python3',str(P/'run-thread-audit.py'),str(P/'J-stx4.json'),str(P/'sources-stx4/PV_LIB_SLICE_RawAudit4.lean')]
# This wrapper is unchanged from the accepted earlier raw attempts.
assert sha(P/'run-thread-audit.py') == 'WRAPPER_SHA'
with (E/f'out-{a}.log').open('w') as out:r=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT,cwd=P)
rec=dict(attempt=a,target='PV_LIB_SLICE_RawAudit4: session4 new statement and source7 joint roots',runtime_audit=True,source_revision=x['revision'],command=cmd,exit=r.returncode,accepted=r.returncode==0,stream_b_turn=x['turn'],source_sha256=sha(P/'sources-stx4/PV_LIB_SLICE_RawAudit4.lean'))
for line in (E/f'time-{a}.log').read_text().splitlines():
 for key,field in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
  if key in line:rec[field]=line.split(key)[1].strip()
rec['axioms_summary_based']=[l for l in (E/f'out-{a}.log').read_text().splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
(E/f'receipt-{a}.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items() if k!='axioms_summary_based'}));print((E/f'out-{a}.log').read_text()[-3000:]);sys.exit(r.returncode)
'''
import hashlib
wrapper=subprocess.check_output(['git','show','5e397cb3878:tools/pv-lib-20261107/run-thread-audit.py'])
code=code.replace('WRAPPER_SHA',hashlib.sha256(wrapper).hexdigest())
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(payload),capture_output=True,text=True)
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
for kind,suffix in [('id-audit','json'),('receipt','json'),('out','log'),('time','log'),('admission','json'),('admission','log')]:
 q=subprocess.run(['ssh',host,f'cat {H}/evidence/{kind}-{a}.{suffix}'],capture_output=True)
 if q.returncode==0:(E/f'{kind}-{a}.{suffix}').write_bytes(q.stdout)
print(r.stdout[-4500:]);print(r.stderr[-1000:]);sys.exit(r.returncode)
