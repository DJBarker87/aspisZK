"""Focused capped Lean job. No failed source is repeated; receipts are recovered."""
from pathlib import Path
import subprocess,json,hashlib,re,shlex,sys,time
E=Path('evidence/pv-stx-20261104');H='/home/dombarker/project-offloads/codex-pv-stx-20261104'
a=int(sys.argv[1]);m=sys.argv[2];assert 91700<=a<=91799 and m.startswith('PV_STX_')
assert not (E/f'submission-{a}.json').exists()
raw=Path('lean/'+m+'.lean').read_bytes();digest=hashlib.sha256(raw).hexdigest()
assert subprocess.check_output(['git','show','HEAD:lean/'+m+'.lean'])==raw
prep=E/('prepare-'+m+'.json');assert json.loads(prep.read_text())['result']['source_sha256']==digest
for p in E.glob('receipt-*.json'):
 r=json.loads(p.read_text());assert r.get('accepted') or r.get('source_sha256')!=digest or (r.get('failure_class')=='pre-elaboration environment' and r.get('environment_correction')),'unchanged failed source'
for p in E.glob('refusal-*.json'):
 assert time.time()-json.loads(p.read_text())['epoch']>=180,'cooldown'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=PV_STX_{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/time-{a}.log','timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',H+'/J.json',H+'/objects',H+'/sources',H+'/objects/'+m+'.olean',H+'/sources/'+m+'.lean','7000']
if a == 91799:
 assert m == 'PV_STX_AuditDriver'
 cmd=cmd[:cmd.index('python3')]+['python3',H+'/run-audit.py',H+'/J.json',H+'/sources/'+m+'.lean']
intent=dict(attempt=a,target=m,source_revision=rev,source_sha256=digest,command=cmd,deps_fingerprint=hashlib.sha256(prep.read_bytes()).hexdigest())
(E/f'submission-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
def ssh(cmd):return subprocess.run(['ssh','dombarker@100.108.41.90',cmd],capture_output=True,text=True)
# Check every stream's receipt names, not only this job's journal.
code='''from pathlib import Path
import re,json
root=Path('/home/dombarker/project-offloads');a=ATTEMPT
pat=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)')
hits=[str(q) for job in root.glob('codex-*') for q in job.glob('evidence/**/*') if q.is_file() and pat.search(q.name)]
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]==str(a)]
print(json.dumps(dict(hits=hits,sent=lines)))
'''.replace('ATTEMPT',str(a))
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
(E/f'id-audit-{a}.json').write_text(r.stdout);x=json.loads(r.stdout);assert not x['hits'] and not x['sent'],x
admit=f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/admission-{a}.json > {H}/evidence/admission-{a}.log 2>&1'
check='python3 -c '+shlex.quote('import json;assert json.load(open('+repr(H+f'/evidence/admission-{a}.json')+'))["allowed"] is True')
r=ssh(admit+' && '+check+' && '+shlex.join(cmd)+f' > {H}/evidence/out-{a}.log 2>&1')
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)))
for name,suffix in [('admission','json'),('out','log'),('time','log')]:
 q=ssh(f'cat {H}/evidence/{name}-{a}.{suffix}');(E/f'{name}-{a}.{suffix}').write_text(q.stdout+q.stderr)
admission=json.loads((E/f'admission-{a}.json').read_text())
if not admission.get('allowed'):
 (E/f'refusal-{a}.json').write_text(json.dumps(dict(epoch=time.time(),exit=r.returncode,admission=admission,compiler_started=False)))
 print('REFUSED uncharged');sys.exit(78)
out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
for key,pat in dict(exit=r'Exit status: (\d+)',peak_rss_kib=r'Maximum resident set size \(kbytes\): (\d+)',swaps=r'Swaps: (\d+)',wall=r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').items():
 v=re.search(pat,tim);intent[key]=v[1] if v else None
intent['print_axioms_summary_based']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
intent['admission']=admission;intent['accepted']=intent['exit']=='0' and 'error:' not in out and 'sorryAx' not in out
if intent['accepted']:
 q=ssh('sha256sum '+shlex.quote(H+'/objects/'+m+'.olean'));assert q.returncode==0,q.stderr
 intent['object_sha256']=q.stdout.split()[0]
(E/f'receipt-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
print(out);print('accepted',intent['accepted']);sys.exit(0 if intent['accepted'] else 1)
