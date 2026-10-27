#!/usr/bin/env python3
"""One focused compile via the existing launcher, with task receipts."""
import hashlib,json,pathlib,re,subprocess,sys,datetime
root=pathlib.Path(__file__).resolve().parents[2]
a=int(sys.argv[1]); m=sys.argv[2]
assert 37100 <= a <= 37399 
module_name=('R1Z.'+m) if m.startswith('PV_Src_') else m
module_path=module_name.replace('.','/')
module_dir=module_path.rsplit('/',1)[0] if '/' in module_path else ''
host='dombarker@100.108.41.90'
job='/home/dombarker/project-offloads/codex-pv-srcid-20261026'
joint='/home/dombarker/project-offloads/aspis-joint-20261019'
t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
e=root/'evidence/pv-srcid3-20261026';e.mkdir(exist_ok=True)
ledger=e/'resume6-attempts.jsonl'
prior=[json.loads(x) for x in ledger.read_text().splitlines()] if ledger.exists() else []
if len(prior)>=97 and m!='PV_Src_FinalAudit':
 print('LAST THREE CHARGED ATTEMPTS RESERVED FOR FULL AUDIT');sys.exit(75)
if ledger.is_file() and len(ledger.read_text().splitlines())>=100:
 print('LEAN BUDGET EXHAUSTED: no host action; zero charge')
 sys.exit(75)
flag=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
if not flag.is_file():
 print('HOST REBUILD GATE CLOSED: no host access or compile; zero charge')
 sys.exit(78)
print('Host restoration instructions: '+flag.read_text(),flush=True)
for prior_path in e.glob('reservation-37*.json'):
 prior=json.loads(prior_path.read_text())
 if prior.get('allowed') is False and prior.get('utc'):
  elapsed=(datetime.datetime.now(datetime.timezone.utc)-datetime.datetime.fromisoformat(prior['utc'].replace('Z','+00:00'))).total_seconds()
  if elapsed<180:
   print('MANDATORY RESERVATION WAIT',180-elapsed);sys.exit(78)
# Fixed user hold applies even if the shared reservation marker disappears.
now=datetime.datetime.now(datetime.timezone.utc)
quiet_until=datetime.datetime(2026,10,26,18,15,tzinfo=datetime.timezone.utc)
if datetime.datetime(2026,10,26,17,45,tzinfo=datetime.timezone.utc) <= now < quiet_until:
 record=dict(attempt=a,module=m,allowed=False,reason='user fixed quiet window until 2026-10-26T18:15:00Z',charged=False,time=now.isoformat())
 (e/f'local-hold-{a}.json').write_text(json.dumps(record)+'\n')
 print(json.dumps(record));sys.exit(78)
src=root/f'docs/research/v8-r0-zk-20261009/lean/{module_path}.lean'
plan=json.loads((e/'resume6-plan.json').read_text())
row=next((x for x in plan['rows'] if x['module']==module_name),None)
if row and row['research_source_exists']:
 data=subprocess.check_output(['git','show',plan['research_revision']+':'+row.get('research_source_path','docs/research/v8-r0-zk-20261009/lean/'+module_path+'.lean')],cwd=root)
 src=e/'sources'/('research-'+m+'.lean')
 src.parent.mkdir(exist_ok=True);src.write_bytes(data)
(e/'sources').mkdir(exist_ok=True)
(e/f'sources/{a}.lean.txt').write_bytes(src.read_bytes())
def ssh(s): return subprocess.run(['ssh',host,s],capture_output=True,text=True)
g=ssh(f'mkdir -p {job}; python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {job}/reservation-{a}.json > {job}/reservation-{a}.log 2>&1; cat {job}/reservation-{a}.log; test -f {job}/reservation-{a}.json && python3 -c \'import json; raise SystemExit(0 if json.load(open("{job}/reservation-{a}.json"))["allowed"] else 78)\'')
(e/f'reservation-{a}.log').write_text(g.stdout+g.stderr)
subprocess.run(['scp','-q',f'{host}:{job}/reservation-{a}.json',str(e/f'reservation-{a}.json')],check=False)
if g.returncode: print(g.stdout,g.stderr);sys.exit(g.returncode)
backup=ssh(f'mkdir -p {job}/snapshots/resume6-{a}; for p in {joint}/sources/{module_path}.lean {joint}/objects/{module_path}.olean; do test ! -f "$p" || cp "$p" {job}/snapshots/resume6-{a}/; done')
assert backup.returncode==0
subprocess.run(['scp','-q',str(src),f'{host}:{joint}/sources/{module_path}.lean'],check=True)
imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
# Fingerprint exact imported objects; retain the individual hashes too.
paths=' '.join(f'{joint}/objects/{i.replace(".","/")}.olean' for i in imports)
d=ssh(f'sha256sum {paths}')
# Missing objects are retained in the fingerprint and diagnosed by Lean.
if d.returncode: d.stdout += d.stderr
fp=hashlib.sha256(d.stdout.encode()).hexdigest()[:16]
r=ssh(f'sh /home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh {a} {module_path} J 7000 8 {fp}')
(e/f'launcher-{a}.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr,flush=True)
exists=ssh(f'test -f {t}/out-{a}.log')
if exists.returncode:
 (e/f'no-scope-{a}.json').write_text(json.dumps(dict(attempt=a,module=module_name,charged=False,exit=r.returncode,reason=r.stdout+r.stderr))+'\n')
 sys.exit(r.returncode or 66)
for name in [f'out-{a}.log',f'time-{a}.log',f'sha-{a}.txt']:
 subprocess.run(['scp','-q',f'{host}:{t}/{name}',str(e/name)],check=False)
out=(e/f'out-{a}.log').read_text() if (e/f'out-{a}.log').exists() else r.stdout
time=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
def metric(pattern):
 x=re.search(pattern,time);return x.group(1) if x else None
ex=re.search(r'exit=(\d+)',out)
record=dict(attempt=a,module=module_path,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_objects=d.stdout.splitlines(),exit=int(ex.group(1)) if ex else r.returncode,wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=metric(r'Swaps: (\d+)'),axioms=[' '.join(s.split()) for s in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)],errors=[s for s in out.splitlines() if 'error' in s],caps=dict(lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
allowed_axioms={'propext','Classical.choice','Quot.sound'}
reported_axioms={name.strip() for line in record['axioms'] for group in re.findall(r'depends on axioms: \[([^\]]*)\]',line) for name in group.split(',') if name.strip()}
record['nonstandard_axioms']=sorted(reported_axioms-allowed_axioms)
record['expected_axiom_reports']=len(re.findall(r'^#print axioms ',src.read_text(),re.M))
record['axiom_reports_complete']=len(record['axioms'])==record['expected_axiom_reports']
if record['exit']==0:
 c=ssh(f'mkdir -p {job}/lean-objects/{module_dir}; cp {joint}/objects/{module_path}.olean {job}/lean-objects/{module_path}.olean; sha256sum {job}/lean-objects/{module_path}.olean')
 record['retained_own_object']=c.stdout.strip();record['object_sha256']=c.stdout.split()[0] if c.stdout.split() else None;assert c.returncode==0
record['research_revision']=plan['research_revision']
record['research_source_exists']=row['research_source_exists'] if row else False
with (e/'resume6-attempts.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
sys.exit(record['exit'] or (1 if record['nonstandard_axioms'] or not record['axiom_reports_complete'] else 0))
