"""Check the two-stage port + declaration isolation without rewriting proofs."""
from pathlib import Path
import json,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');r=json.load(open(D/'isolate-p03-resume5.json'));raw=D/'p03-before-isolation-resume5.lean.txt';assert hashlib.sha256(raw.read_bytes()).hexdigest()==r['raw_failed_sha256']
for row in r['rows']:assert hashlib.sha256(Path(row['source']).read_bytes()).hexdigest()==row['sha256'],row['module']
assert (D/'lean/PV_B3P_P227_03.lean').read_text()=='import PV_B3P_P227_03d\n\n#print axioms PV_B3P_227.reference_poseidon.external_local_packed_raw\n'
print('isolated declaration hashes and aggregator match')
