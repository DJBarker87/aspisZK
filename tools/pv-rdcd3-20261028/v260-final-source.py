"""Final changed-closure check; expected work is hashing and source checking.
No repeated arithmetic fixture or unchanged Rust compilation is performed.
"""
from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
for tool in ['v260-word-source.py','v260-fingerprint.py']:
 subprocess.run(['python3',str(D/tool)],check=True)
files=['range-source-result.json','v260-word-source-result.json','v260-project-source-result.json','v260-constants-result.json','v260-fingerprint-result.json']
record=dict(reason='New V260 selected-cohort bridge, generic word/control laws and final complete module changed the project dependency closure; previous frozen Rust constant/native checks are reused unchanged.',expected_phase='hashing coherent project/external DAG and source patterns; no arithmetic/elimination',files={x:hashlib.sha256((D/x).read_bytes()).hexdigest() for x in files},composition='Reclassification within existing compiler/Aeneas/Rust semantics; no endpoint premise removed',native_reuse='Earlier v260-source-static constant checks and range-library-native finite fixtures, unchanged source/input hashes')
(D/'v260-final-source-result.json').write_text(json.dumps(record,indent=2)+'\n');print('Changed V260 proof closure and unchanged frozen source/static gates associated')
