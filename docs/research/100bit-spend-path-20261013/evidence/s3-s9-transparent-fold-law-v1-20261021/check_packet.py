#!/usr/bin/env python3
"""Portable integrity and source-cut checker for this evidence packet."""
from pathlib import Path
import hashlib, json, sys
ROOT = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
errors=[]
manifest_path=ROOT/'manifest.json'
m=json.loads(manifest_path.read_text())
if m.get('schema') != 'focused-extractor-proof-packet-v1': errors.append('wrong schema')
for rel, meta in m.get('files',{}).items():
    path=ROOT/rel
    if not path.is_file(): errors.append(f'missing file: {rel}'); continue
    data=path.read_bytes()
    if len(data)!=meta.get('bytes'): errors.append(f'size mismatch: {rel}')
    if sha(data)!=meta.get('sha256'): errors.append(f'hash mismatch: {rel}')
for mod in m.get('modules',[]):
    src=ROOT/mod['source']
    if not src.is_file(): errors.append(f"module source missing: {mod['module']}")
    elif sha(src.read_bytes())!=mod['source_sha256']: errors.append(f"module source pin mismatch: {mod['module']}")
    if mod.get('exit_status')!=0: errors.append(f"non-green module: {mod['module']}")
    if mod.get('swap_bytes')!=0: errors.append(f"swap used: {mod['module']}")
for name, imp in m.get('direct_import_source_map',{}).items():
    src=ROOT/imp['source']
    if not src.is_file(): errors.append(f'missing imported source: {name}')
    elif sha(src.read_bytes())!=imp['source_sha256']: errors.append(f'import source pin mismatch: {name}')
# The extracted module must retain the generated source declarations verbatim.
fold=(ROOT/'sources/ExtractedIteratorFoldV1.lean').read_text()
generated=(ROOT/'sources/generated/AspisR1S9FactoredCut/Funs.lean').read_text()
ns='namespace AspisR1S9FactoredCut\n'
start_f=fold.index(ns)+len(ns); end_f=fold.index('\nend AspisR1S9FactoredCut',start_f)
start_g=generated.index(ns)+len(ns)
# The following generated function starts immediately after the three fold declarations.
next_marker='\n/-- [aspis_r1_weights_pair_cut::field::'
end_g=generated.find(next_marker,start_g)
if end_g<0: errors.append('cannot locate generated declaration following fold cut')
elif fold[start_f:end_f] != generated[start_g:end_g]: errors.append('fold declarations differ from generated Funs source')
# The generated Funs has historical resource options; the selected proof owners must not.
for rel in ('sources/ExtractedIteratorFoldV1.lean','sources/TransparentFoldRangeLawV1.lean','sources/TransparentFoldActualOpsConsumerV1.lean'):
    text=(ROOT/rel).read_text()
    if 'set_option maxHeartbeats' in text or 'set_option maxRecDepth' in text: errors.append('resource override in '+rel)
# The full-MIR translation is specifically def_id 52 with a valid output.
llbc=json.loads((ROOT/'extraction/generated/translation.json').read_text())
# This Aeneas translation schema has no has_errors field; the checked Charon/Aeneas receipts record declaration_check_ok=true and exit_status=0.
for phase in ('charon','aeneas'):
    receipt=json.loads((ROOT/f'extraction/runs/{phase}/receipt.json').read_text())
    if receipt.get('exit_status')!=0 or receipt.get('declaration_check_ok') is not True: errors.append(phase+' extraction receipt is not green')
if not any(x.get('def_id')==52 for x in llbc.get('functions',[])):
    # Translation JSON schemas differ; fall back to a textual name/id check.
    raw=(ROOT/'extraction/generated/translation.json').read_text()
    if '"def_id": 52' not in raw or 'Iterator::fold' not in raw: errors.append('fold def_id 52 missing from translation metadata')
if errors:
    print('\n'.join('FAIL: '+e for e in errors)); sys.exit(1)
print(f"PASS: {len(m['files'])} file hashes, {len(m['modules'])} Lean receipts, {len(m['direct_import_source_map'])} imported source pins, exact generated fold cut, LLBC and option checks")
