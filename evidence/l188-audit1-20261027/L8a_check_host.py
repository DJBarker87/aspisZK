"""Run the unmodified retained extraction checker with minimal symlink layout."""
from pathlib import Path
import json,subprocess,time,hashlib
import L8a_attempt as a
E=a.E; B=a.B; A='L8a_Check001'
# Admission always precedes input staging. No simultaneous scope for this job.
for retry in range(11):
 r=a.ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{A}-reservation.json > {B}/{A}-barrier-{retry}.log 2>&1')
 a.collect(A+f'-barrier-{retry}.log')
 exists=a.ssh(f'test -f {B}/{A}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if r.returncode==0:a.collect(A+'-reservation.json');break
 if r.returncode==78 and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 log=(E/(A+f'-barrier-{retry}.log')).read_text()
 if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
 raise RuntimeError('STOP admission: '+log)
else:raise RuntimeError('reservation retries exhausted')
files=['L8a_check-extraction.py','L8a_V6-Funs.lean.txt','L8a_JoinSource.lean.txt','L8a_JoinReceipt.json','L8a_JoinPreflight.json']
r=a.ssh(f'mkdir -p {B}/L8a_check_inputs');assert r.returncode==0,r.stderr
for f in files:
 r=subprocess.run(['scp','-q',*a.SSH,str(E/f),a.H+':'+B+'/L8a_check_inputs/'+f],capture_output=True,text=True);assert r.returncode==0,r.stderr
payload=r'''from pathlib import Path
import hashlib,json
B=Path(%r);C=B/'L8a_check_layout';X=C/'s4-minimal-fixed-calls-v10-20261021/extraction';X.mkdir(parents=True,exist_ok=False)
I=B/'L8a_check_inputs';old=Path('/home/dombarker/project-offloads/s4-minimal-fixed-calls-v10-extraction-20261021')
links={X/'L8a_check-extraction.py':I/'L8a_check-extraction.py',X/'evidence/four_dots.llbc':old/'four_dots.llbc',X/'evidence/generated':old/'generated',X/'evidence/runs-charon-retry5':old/'runs-charon-retry5',X/'evidence/runs-aeneas-retry6':old/'runs-aeneas-retry6',C/'s4-four-dots-fixed-call-v2/sources/FourDotsFixedV6-Funs.lean':I/'L8a_V6-Funs.lean.txt',X/'evidence/tail-literal-run-join-v1/sources/S4TailLiteralJoinV1.lean':I/'L8a_JoinSource.lean.txt',X/'evidence/tail-literal-run-join-v1/receipt.json':I/'L8a_JoinReceipt.json',X/'evidence/tail-literal-run-join-v1/preflight.json':I/'L8a_JoinPreflight.json'}
for dst,src in links.items():
 assert src.exists(),src
 dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
# Symlink resolve() in checker requires a real script at the layout location.
p=X/'L8a_check-extraction.py';p.unlink();p.write_bytes((I/'L8a_check-extraction.py').read_bytes())
cfg=json.loads(%r);cfg['command']=['python3',str(p)]
(B/(cfg['attempt']+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps({str(k):str(v) for k,v in links.items()},indent=2))
'''
cfg=dict(kind='extraction-check',module='L8a_retained_extraction_check',attempt=A,sources=['L8a_check_inputs/'+f for f in files],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),timeout=180,deps_fingerprint={'checker_sha256':hashlib.sha256((E/'L8a_check-extraction.py').read_bytes()).hexdigest(),'scope':'Retained v10 checker, no new extraction; cannot certify PublicPreparation'},expected_time='Python manifest, archived successful receipts and executable-body byte comparison; no compilation or arithmetic step',reservation_retries=retry)
r=a.ssh('python3 -',payload%(B,json.dumps(cfg)));assert r.returncode==0,r.stderr
(E/'L8a_CheckLayout.json').write_text(r.stdout);a.collect(A+'.json')
r=a.ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {A}.json')
(E/(A+'-launcher.log')).write_text(r.stdout+r.stderr)
for f in ['receipt.json','stdout.log','time.log']:a.collect(A+'/'+f)
print((E/A/'stdout.log').read_text(),flush=True)
