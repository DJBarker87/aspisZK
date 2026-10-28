"""Stage a native finite differential using byte-verified, read-only core sources."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
assert json.loads((E/'encoder-core-source-check.json').read_text())['all_match']
r=subprocess.run(['ssh',H,f'mkdir -p {D}/stage-encoder; python3 {G}/reservation.py {D}/stage-encoder/admission.json > {D}/stage-encoder/reservation.log 2>&1'])
a=subprocess.check_output(['ssh',H,f'cat {D}/stage-encoder/admission.json'],text=True);(E/'stage-encoder-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:sys.exit(78)
subprocess.run(['ssh',H,f'mkdir -p {D}/encoder-proof'],check=True)
for f in ['encoder-native.rs','owned-encoder.rs']:
 subprocess.run(['scp',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+'/encoder-proof/'+f],check=True)
subprocess.run(['scp',str(R/'tools/pv-dlib-20261028/EncoderCargo.toml.txt'),H+':'+D+'/encoder-proof/Cargo.toml'],check=True)
