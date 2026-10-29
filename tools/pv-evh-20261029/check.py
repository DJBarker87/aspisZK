"""D502 source audit: no native or release-closure claims."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-evh-20261029')
old='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean'
assert subprocess.check_output(['git','show','ae30a1421e:'+old])==Path(old).read_bytes()
oldsha=hashlib.sha256(Path(old).read_bytes()).hexdigest()
files=sorted(Path('lean').glob('PV_EVH_*.lean'))
for p in files:
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',s,re.M),p
 for doc in re.findall(r'/-(?:-|!)(.*?)-/',s,re.S):
  assert 'adopted by owner decision D502/D478' in doc,(p,doc)
 assert not re.search(r'set_option (maxRecDepth|maxHeartbeats|exponentiation.threshold)',s),p
bound=Path('lean/PV_EVH_Core.lean').read_text().split('def bound : ℚ :=',1)[1].split('/--',1)[0].strip()
prior=Path('lean/PV_EVHD_Headline.lean').read_text().split('def bound : ℚ :=',1)[1].split('/--',1)[0].strip()
assert bound==prior
assert 'ProverCommitModelCore16.core_privacy' in Path('lean/PV_EVH_Core.lean').read_text()
assert 'ProverCommitReencode16.privacy_transport' in Path('lean/PV_EVH_Core.lean').read_text()
assert 'simE (h).transport B outputs x' in Path('lean/PV_EVH_Core.lean').read_text()
rt=Path('lean/PV_EVH_Deployed.lean').read_text()
names=re.findall(r'^def ([A-Z][A-Z0-9_]+)',Path('lean/PV_RJ4IDB_OpenInputs.lean').read_text(),re.M)
assert len(names)==9
for n in names: assert 'OpenInputs.'+n in rt,n
request=json.load(open(E/'AGG16-REQUEST.json'))
assert request['source_sha256']==hashlib.sha256(Path(request['source']).read_bytes()).hexdigest()
assert not any(json.load(open(q)).get('target')=='PV_EVH_FixtureConsumer' for q in E.glob('submission-*.json'))
changed=subprocess.check_output(['git','diff','--name-only','ae30a1421e'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
records=[]
for p in files:
 records.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size,worker_compile_forbidden=p.name=='PV_EVH_FixtureConsumer.lean'))
(E/'source-check.json').write_text(json.dumps(dict(status='PASS: source checks only',historical_headline_sha256=oldsha,bound_identical=True,nine_inputs=names,modules=records,changed_paths=changed),indent=2)+'\n')
print('PASS: protected headline, identical bound, nine inputs, docstrings, forbidden constructs, size and lead-only consumer')
