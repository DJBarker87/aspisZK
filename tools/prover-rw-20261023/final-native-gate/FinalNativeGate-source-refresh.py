"""LOCAL TEXT ONLY: refresh acyclic candidate plan/bootstrap transfer pins.

No runtime approval. Root seal hashes must be checked against committed source
manifest by the later transfer reviewer, under existing bootstrap trust boundary.
"""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
STAGE='/home/dombarker/final-native-gate-v13-20261025/'
def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))
def write(path,value):path.write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
p=json.loads((D/'FinalNativeGate-plan.json').read_text())
# No self-hash: plan and two root seals are independently carried by transfer.
source=[x for x in sorted(D.glob('*.py')) if x.name not in ('FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py')]
for path in list(p['files']):
    if path.startswith('/home/dombarker/final-native-gate-v12-20261025/') or path.startswith('/home/dombarker/final-native-gate-v11-20261025/') or path.startswith('/home/dombarker/final-native-gate-v13-20261025/') or path.startswith('/home/dombarker/final-native-gate-v8-20261025/') or path.startswith('/home/dombarker/final-native-gate-v7-20261025/') or path.startswith('/home/dombarker/final-native-gate-v6-20261025/') or path.startswith('/home/dombarker/final-native-gate-v5-20261025/') or path.startswith('/home/dombarker/final-native-gate/') or path.startswith(STAGE) or path.startswith('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate/'):del p['files'][path]
p['job_source_sizes']={}
for x in source:
    value=pin(x.read_bytes());p['files'][STAGE+x.name]=value['sha256'];p['job_source_sizes'][STAGE+x.name]=value['size']
# Source025 adds only cd7d bounded complete-capture retries.
p['job_revision']='92a0cfa06c plus Source032 DATA operational traversal overlay'
p['setup_environment']=dict(HOME='/home/dombarker',USER='dombarker',LOGNAME='dombarker',PATH='/usr/bin:/bin',LANG='C.UTF-8',LC_ALL='C.UTF-8')
p['bootstrap_source_boundary']='Plan excludes own/seal/bootstrap hashes. Bootstrap manifest pins plan+plan seal+finite job transfer source; bootstrap seal excluded. Both root seal bytes require independent transfer/source-manifest review. Operational pin observation is not executed-bytecode semantics.'
p['setup_deferred']=['candidate UID/bus/runtime/tool/ELF dependency roles and selected cache fingerprint data require lead review; DATA never grants execution']
p['setup_catalog_roots']=sorted(set(p['native_roots'])|set(p['files']))
p['missing']=[x for x in p['missing'] if 'shutdown binding implementation' not in x]
write(D/'FinalNativeGate-plan.json',p)
(D/'FinalNativeGate_seal.py').write_text('PLAN_SHA256 = '+repr(pin((D/'FinalNativeGate-plan.json').read_bytes())['sha256'])+'\n')
# Local package/transfer pinset independent of target/harness files in plan.
rows={x.name:pin(x.read_bytes()) for x in sorted(D.iterdir()) if x.is_file() and x.name not in ('FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py')}
write(D/'FinalNativeGate-bootstrap.json',rows)
(D/'FinalNativeGate_bootstrap_seal.py').write_text('BOOTSTRAP_SHA256 = '+repr(pin((D/'FinalNativeGate-bootstrap.json').read_bytes())['sha256'])+'\n')
