from pathlib import Path
import json,subprocess,time
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-trace-proof-20261018')
raw=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=active','--no-legend','--plain'],text=True)
units=[];total=8*2**30
for line in raw.splitlines():
 name=line.split()[0]
 if name=='init.scope':continue
 vals=subprocess.check_output(['systemctl','--user','show',name,'-p','MemoryMax','-p','MemoryHigh','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
 d=dict(x.split('=',1) for x in vals.splitlines());units.append({'unit':name,**d});assert d['MemoryMax']!='infinity',(name,d);total+=int(d['MemoryMax'])
assert total<55*2**30,total
record={'utc':time.time(),'scope':'c-source-trace-20261018.scope','MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'aggregate_memory_max_bytes':total,'active_user_scopes':units,'free':subprocess.check_output(['free','-b'],text=True),'shared_lock':'/tmp/aspis-r0-lean.lock','intended_target':'R1UnifiedSemanticRecoveryCore,R1InitialWalkTrace,TraceAppend,ExtractedSourceDigestOracle','expected_new_targets':7,'reuse_predecessors':0,'source_revision':'a555c852664c80000942f0c911e16719a5493625'}
(W/'launch-reservations-source-trace.json').write_text(json.dumps(record,indent=2)+'\n')
with (W/'serial-source-trace.log').open('w') as log:
 rc=subprocess.call(['systemd-run','--user','--scope','--unit=c-source-trace-20261018','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','/usr/bin/python3',str(W/'serial-host.py')],stdout=log,stderr=subprocess.STDOUT)
print('source read serial exit',rc)
raise SystemExit(rc)
