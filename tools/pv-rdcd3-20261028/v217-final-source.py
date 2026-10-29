"""Final changed proof-cohort hashing and new evidence association, no arithmetic.
Previously passed source-body gates are reused unchanged after source hash checks.
"""
from pathlib import Path
import json,hashlib,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
reuse=json.load(open(D/'v217-native-reuse.json'));S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
for name,pin in reuse['files'].items():assert sha(S/name)==pin,(name,pin)
outputs=['v217-application-source-result.json','v217-field-source-result.json','v217-library-source-result.json','range-source-result.json','library-source-result.json','v260-word-source-result.json','v265-source-result.json']
for name in outputs:
 j=json.load(open(D/name))
 if 'source_path' in j:assert sha(Path(j['source_path']))==j['source_sha256']
 for rec in j.get('records',[]):
  if 'path' in rec:
   pin=rec.get('source_sha256',rec.get('file_sha256'))
   assert pin and sha(Path(rec['path']))==pin,(name,rec['path'])
field=json.load(open(D/'v217-field-source-result.json'))
assert sha(D/'lean-sources/R1Z/PV_RDCD3_FieldSource.lean')==field['owned_model_sha256']
assert sha(D/'lean-sources/R1Z/PV_RDCD3_CB_MaskSource.lean')=='f8f1c6ce75cc8c6a64c747b780c9962a1df8d77fa99e33e532e13f5986aeeb9d'
assert sha(D/'lean-sources/R1Z/PV_RDCD3_CB_OwnedMask.lean')=='7ab37bd343a9c5a860ee0ee21f25ff23332bf2314080ac1112d0fa1c8d489e5d'
features=sha(D/'deployed-client-features.json')
for name in ['v217-field-source-result.json','v217-library-source-result.json']:
 assert json.load(open(D/name))['feature_graph_sha256']==features
subprocess.run(['python3',str(D/'v217-fingerprint.py')],check=True)
j=dict(files={n:sha(D/n) for n in outputs+['v217-fingerprint-result.json','v217-native-reuse.json']},scope='Complete V217 changed proof closure and unchanged deployed source/value/Result bindings only; no binary/world/observer theorem',compiler_boundary='V370 and owner D381/D386 retained by name',drop_bindings='Field/newtype/array data are Copy with no user Drop. ops::Range<usize> contains two usize scalars; Rev contains only that range. Their complete source construction/control records introduce no owning allocation or callback destructor. Trivial drop glue is erased at the retained source-value projection; panic/world/observer effects are not claimed.',composition='Reclassification within existing Aeneas/Rust semantic trust, zero endpoint premise removal',native_reuse='Prior original/reference arithmetic finite fixtures; no new arithmetic launch or Kani recredit')
(D/'v217-final-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print('V217 proof DAG, exact model source and unchanged finite native input pins associated')
