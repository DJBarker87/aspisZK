from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((E/'final-manifest.json').read_text())
records={int(re.search(r'J(\d+)',p.name)[1]):json.loads(p.read_text()) for p in (E/'lean').glob('J*.json')}
assert set(records)==set(range(10700,10775))|{10798}
for row in m['roots']:
 p=Path(row['path']);assert sha(p)==row['sha256']
 r=records[int(row['accepted_attempt'][1:])]
 assert r['exit']==0 and r['source_sha256']==sha(p)
 assert p.read_bytes()==(E/'lean'/(r['attempt']+'.lean.txt')).read_bytes()
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(?:maxRecDepth|maxHeartbeats)',p.read_text(),re.M)
 for dep,path,h in r['dependencies']:
  if dep in {x['module'] for x in m['roots']}:
   latest=next(x for x in m['roots'] if x['module']==dep)
   # Direct final audit pins the current object for every new source; historical receipts remain retained.
   assert any(d==dep and dh==h for d,dp,dh in records[10798]['dependencies']),('stale dependency',row['module'],dep)
audit=records[10798];assert audit['exit']==0
p=L/'R1Z/ProverCommitAudit55.lean';assert sha(p)==audit['source_sha256']
allowed={'propext','Classical.choice','Quot.sound'};axioms={}
for name,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit['out']):
 vals={x.strip() for x in ax.split(',') if x.strip()};assert vals<=allowed,(name,vals);axioms[name]=sorted(vals)
for name in re.findall(r"'([^']+)' does not depend on any axioms",audit['out']):axioms[name]=[]
assert set(axioms)==set(m['theorems'])|{'R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed'}
endpoint=L/'R1Z/ProverCommitDeployedFuel22.lean'
assert endpoint.read_bytes()==(E/'endpoint/before.lean.txt').read_bytes()==(E/'endpoint/after.lean.txt').read_bytes()
assert subprocess.check_output(['git','diff','341584654f','--name-only','--','crates','programs'])==b''
for path,r in json.loads((E/'final-source-pins.json').read_text())['pins'].items():assert sha(Path(path))==r['sha256']
for p in E.rglob('*'):
 if p.is_file() and '__pycache__' not in p.parts:
  assert p.suffix not in {'.olean','.o','.so','.a','.rlib','.llbc','.tar','.gz','.zip','.elf'},p
inventory=[dict(attempt='J'+str(n),module=r.get('module'),exit=r.get('exit'),compiler_invoked=r.get('compiler_invoked'),reason=r.get('reason'),source_sha256=r.get('source_sha256')) for n,r in sorted(records.items())]
(E/'attempt-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
result=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_roots=len(m['roots']),new_theorems=len(m['theorems']),axiom_reports=len(axioms),axioms=axioms,audit_attempt='J10798',endpoint_sha256=sha(endpoint),shipped_changes=False,attempt_records=len(records),unused_attempts=['J'+str(n) for n in range(10700,10800) if n not in records],scope=m['scope'],target_established=False)
(E/'final-integrity.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='axioms'}))
