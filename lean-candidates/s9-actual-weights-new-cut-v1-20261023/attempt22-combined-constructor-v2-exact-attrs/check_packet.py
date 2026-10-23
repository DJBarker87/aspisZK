#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
W=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert (W/'check_sourcecut.py').exists()
import subprocess
r=subprocess.run([sys.executable,str(W/'check_sourcecut.py')],capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
manifest=json.loads((W/'manifest.json').read_text())
assert manifest['schema']=='focused-extractor-proof-packet-v1'
assert manifest['compiled_objects_included'] is False
assert manifest['source_revision']== '2409d9cc057563b73d4cb119f05e54a177b74636'
assert manifest['theorem_state']=='draft_uncompiled'
for phase in ('charon','aeneas'):
 receipt=json.loads((W/'evidence'/phase/'receipt.json').read_text())
 assert receipt['exit_status']==0 and receipt['swap_current_bytes']==0
 assert receipt['limits']=={'memory.high':'1073741824','memory.max':'2147483648','memory.swap.max':'0'}
 assert (W/'evidence'/phase/'command.json').exists()
assert json.loads((W/'evidence/charon/declaration-inventory.json').read_text())['raw_llbc_retained'] is False
inventory=json.loads((W/'evidence/charon/declaration-inventory.json').read_text())
assert inventory['has_errors'] is False
assert len(inventory['target_declarations'])==2
assert all(x['opacity']=='Transparent' for x in inventory['target_declarations'])
a=json.loads((W/'evidence/aeneas/receipt.json').read_text())
assert a['generated_lean']['generated/AspisR1S9ActualWeightsNewBoxNewV3/Funs.lean']=='e3afb40c399755adc788ebe756036acd3823c9f2871c2814c0b93a18371c25e8'
assert a['generated_lean']['generated/AspisR1S9ActualWeightsNewBoxNewV3/Types.lean']=='7c70eab6b17221dbb51b14ff742a0e5a16859e6b3ec1ca71f4bcc1fbe7cbdfa2'
for name in ('Funs.lean','Types.lean'):
 raw=W/'generated/AspisR1S9ActualWeightsNewBoxNewV3'/name
 clean=W/'generated/normalized'/name
 s=raw.read_text()
 expected=s.replace('/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n\n','')
 expected=expected.replace('/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n\n','')
 # Python literal above represents backslash-n: use exact newline strings as well.
 expected=s.replace('/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n\n','')
 expected=expected.replace('/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n\n','')
 assert clean.read_text()==expected,(name,'normalization is not exact override removal')
 assert 'set_option maxHeartbeats' not in clean.read_text() and 'set_option maxRecDepth' not in clean.read_text()
funs=(W/'generated/normalized/Funs.lean').read_text()
types=(W/'generated/normalized/Types.lean').read_text()
assert 'def weights_new\n' in funs and 'Weights.box_from_parts' in funs
assert 'def Weights.box_from_parts' in funs
assert 'structure Weights where' in types and 'inductive Error where' in types
proof=W/'sources/S9ActualWeightsNewExtraExactV4.lean'
assert proof.exists() and '#print axioms weights_new_extra_exact_v4' in proof.read_text()
assert sha(proof)==manifest['theorem_source_sha256']
for q in W.rglob('*'):
 if not q.is_file(): continue
 assert q.suffix not in ('.olean','.ilean','.ir','.server','.llbc','.so','.dylib','.bin','.o'),q
 assert '__pycache__' not in q.parts
print('PASS: exact constructor source pins, successful capped Charon/Aeneas receipts, transparent nonempty target declarations, normalized Lean source, and source-only packet contents.')
print('PENDING: Lean compile/#print axioms for ExtraExactV4; fixed [7,6] source normalization; full helper/caller source binding; Box allocation-error refinement.')
