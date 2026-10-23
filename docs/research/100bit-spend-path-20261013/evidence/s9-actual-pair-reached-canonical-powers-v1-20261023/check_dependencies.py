from pathlib import Path
import json,hashlib,re,subprocess,sys
r=Path(__file__).resolve().parent;base=r.parent.parent
d=json.loads((r/'source-dependencies.json').read_text())
for x in d['exact_sources']:assert hashlib.sha256((base/x['path']).read_bytes()).hexdigest()==x['sha256']
rows=json.loads((r/'portability/selection.json').read_text())
assert len(rows)==4
for x in rows:
 p=r/'proof/native-reachability/sources'/(x['module']+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256']
receipt=json.loads((r/'proof/native-reachability/receipt.json').read_text());main=next(x for x in rows if x['module']=='S9ActualPairReachedFactoredHelperV1')
assert receipt['exit_status']==0 and receipt['scope_swap_peak_bytes']==0 and receipt['source_sha256']==main['source_sha256'] and receipt['object_sha256']==main['sha256']
log=(r/'proof/native-reachability/lean.log').read_text();assert 'sorryAx' not in log and 'error:' not in log
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
assert all(x['identical'] for x in json.loads((r/'portability/cohort-identity.json').read_text())['exact_byte_identity_anchors'])
subprocess.check_call([sys.executable,str(base/'evidence/s9-actual-powers-four-canonical-v1-20261023/check_packet.py')])
print('PASS: exact actual reached-helper sources, NUC receipt and powers source dependencies')
