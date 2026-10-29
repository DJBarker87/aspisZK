"""adopted by owner decision D502/D478. D502 adopted: Single-module capped invocation; admission and original receipt recovery."""
from pathlib import Path
import subprocess,json,shlex,sys,time,hashlib,re
E=Path('evidence/pv-evh2-20261029'); H='/home/dombarker/project-offloads/codex-pv-evh-20261029';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);assert 70800<=a<=70899
assert not (E/f'submission-{a}.json').exists()
module=sys.argv[2] if len(sys.argv)>2 else 'PV_EVH_Interface'
assert module.startswith('PV_EVH_')
assert module != 'PV_EVH_FixtureConsumer', 'lead-only 16 GiB consumer; worker launch forbidden'
if a >= 70897:
 assert module in ['PV_EVH_BindingAudit','PV_EVH_BindingReplay','PV_EVH_OwnedAudit'], 'reserved audit ID'
source=Path('lean/'+module+'.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()==json.load(open(E/('prepare-'+module+'.json')))['result']['source_sha256']
# Ruling (u): source-only guard, including all failures in this line.
source_sha=hashlib.sha256(source).hexdigest()
for prior in E.glob('refusal-*.json'):
 assert time.time()-json.loads(prior.read_text())['epoch']>=180, 'admission cooldown active'
for prior in list(E.glob('receipt-*.json')) + list(Path('evidence/pv-evh-20261029').glob('receipt-*.json')):
 old=json.loads(prior.read_text())
 assert old.get('accepted') or old.get('source_sha256')!=source_sha or (old.get('failure_class')=='pre-elaboration environment' and old.get('environment_correction')),  ('unchanged failed source',str(prior))
assert subprocess.check_output(['git','show','HEAD:lean/'+module+'.lean'])==source
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
code="""import pathlib,re,json
root=pathlib.Path('/home/dombarker/project-offloads');hits=[];a=ATTEMPT
pat=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)')
for job in root.glob('codex-pv-*'):
 for q in job.glob('evidence/**/*'):
  if q.is_file() and pat.search(q.name):hits.append(str(q))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]==str(a)]
print(json.dumps(dict(attempt=a,receipt_hits=hits,sent_hits=lines)))
""".replace('ATTEMPT',str(a))
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
idcheck=json.loads(r.stdout);(E/f'id-audit-{a}.json').write_text(r.stdout)
# Ruling (m'): own refused admission files do not consume an ID.
refused=E/f'refusal-{a}.json'
if refused.exists() and not json.loads(refused.read_text())['compiler_started']:
 allowed={H+f'/evidence/admission-{a}.json',H+f'/evidence/admission-{a}.log'}
 idcheck['uncharged_own_admission_files']=[p for p in idcheck['receipt_hits'] if p in allowed]
 idcheck['receipt_hits']=[p for p in idcheck['receipt_hits'] if p not in allowed]
 (E/f'id-audit-{a}.json').write_text(json.dumps(idcheck))
assert not idcheck['receipt_hits'] and not idcheck['sent_hits']
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-evh-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/time-{a}.log','timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',H+'/J.json',H+'/objects',H+'/sources',H+'/objects/'+module+'.olean',H+'/sources/'+module+'.lean','7000']
intent=dict(attempt=a,target=module,source_revision=rev,source_path='lean/'+module+'.lean',source_git_blob=subprocess.check_output(['git','rev-parse',rev+':lean/'+module+'.lean'],text=True).strip(),source_sha256=hashlib.sha256(source).hexdigest(),command=cmd)
(E/f'submission-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
admit=f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/admission-{a}.json > {H}/evidence/admission-{a}.log 2>&1'
check='python3 -c '+shlex.quote('import json; assert json.load(open('+repr(H+f'/evidence/admission-{a}.json')+'))["allowed"] is True')
remote=admit+' && '+check+' && '+shlex.join(cmd)+f' > {H}/evidence/out-{a}.log 2>&1'
r=ssh(remote);(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)))
for name in ['admission','out','time']:
 suffix='json' if name=='admission' else 'log'
 q=ssh(f'cat {H}/evidence/{name}-{a}.{suffix}')
 (E/f'{name}-{a}.{suffix}').write_text(q.stdout+q.stderr)
admission=json.load(open(E/f'admission-{a}.json'))
if not admission.get('allowed'):
 refusal=dict(epoch=time.time(),admission=admission,admission_exit=r.returncode,compiler_started=False)
 (E/f'refusal-{a}.json').write_text(json.dumps(refusal))
 (E/f'refusal-history-{a}-{int(refusal["epoch"])}.json').write_text(json.dumps(refusal))
 (E/f'submission-{a}.json').unlink();print('REFUSED uncharged; full 180s cooldown');sys.exit(78)
tim=(E/f'time-{a}.log').read_text();out=(E/f'out-{a}.log').read_text()
for key,pat in dict(exit=r'Exit status: (\d+)',peak_rss_kbytes=r'Maximum resident set size \(kbytes\): (\d+)',swaps=r'Swaps: (\d+)',wall=r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').items():
 m=re.search(pat,tim);intent[key]=m[1] if m else None
intent['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
intent['deps_fingerprint']=hashlib.sha256((E/('prepare-'+module+'.json')).read_bytes()).hexdigest()
intent['admission']=admission;intent['accepted']=intent['exit']=='0' and 'error:' not in out and 'sorryAx' not in out
if intent['accepted']:
 q=ssh('sha256sum '+H+'/objects/'+module+'.olean');assert q.returncode==0,q.stderr
 intent['object_sha256']=q.stdout.split()[0]
(E/f'receipt-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
print(out);print(json.dumps({k:v for k,v in intent.items() if k not in ['admission','command']},indent=2));sys.exit(0 if intent['accepted'] else 1)
