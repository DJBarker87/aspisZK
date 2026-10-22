#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, subprocess, sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'s4-early-powers-generated-full-tx2-fields-d18-v1-20261022'

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

m=json.loads((ROOT/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
# The base packet is immutable and independently checked.
assert sha(BASE/'manifest.json')==m['base_candidate_packet']['manifest_sha256']
assert sha(BASE/'producer/import-closure/closure.json')==m['base_candidate_packet']['import_closure_sha256']
subprocess.run([sys.executable,str(BASE/'check_packet.py')],check=True,capture_output=True,text=True)
# New theorem source/object receipt and exact standard-only axiom log.
entry=next(x for x in m['modules'] if x['module']=='S4EarlyPowersSelectedPackedTxConsumersD18V1')
receipt=json.loads((ROOT/'producer/selected-consumer/accepted-receipt.json').read_text())
assert sha(ROOT/entry['source'])==entry['source_sha256']==receipt['source_sha256']
assert entry['object_sha256']==receipt['object_sha256']
assert receipt['exit_status']==0 and receipt['swap_bytes']==0
assert entry['axioms']==['propext','Classical.choice','Quot.sound']
log=(ROOT/'producer/selected-consumer/lean.log').read_text()
assert 'sorryAx' not in log
assert 'depends on axioms: [propext,' in log and 'Classical.choice' in log and 'Quot.sound' in log
# The accepted selected-return and format-alignment owners used by this compile.
owner=json.loads((ROOT/'producer/owner-pins.json').read_text())
for module,sourcefile,objfile in [
 ('S4SelectedPackedReturnV1',ROOT/'dependencies/S4SelectedPackedReturnV1.lean',None),
 ('S4FormatPayloadAlignmentV1',ROOT/'dependencies/S4FormatPayloadAlignmentV1.lean',None)]:
    pin=owner[module]
    assert sha(sourcefile)==pin['source_sha256']
    assert Path(pin['object_path']).is_file() and sha(pin['object_path'])==pin['object_sha256']
    r=json.loads((ROOT/pin['producer_receipt']).read_text())
    assert r['exit_status']==0 and r['source_sha256']==pin['source_sha256'] and r['object_sha256']==pin['object_sha256']
# The selected profile is the exact checked 7,520-owner closure. Only the delta
# from the parent packet is stored here; the full parent closure remains pinned above.
ext=json.loads((ROOT/'producer/closure-extension.json').read_text())
assert ext['base_closure_sha256']==m['base_candidate_packet']['import_closure_sha256']
assert ext['selected_consumer_modules']==7520 and ext['selected_consumer_missing']==[]
assert ext['new_selected_owner_count']==len(ext['new_selected_owners'])==m['incremental_selected_profile']['modules']
assert m['incremental_selected_profile']['missing']==0
summary=json.loads((ROOT/'producer/selected-consumer/closure-check-result.json').read_text())
assert summary['modules']==7520 and summary['missing']==[] and summary['full_closure_retained'] is False
# Source-only packet rule.
assert not list(ROOT.rglob('*.olean'))
print('PASS: base generated-powers packet, selected-return composition, exact owner pins, standard axioms, and zero-missing selected closure')
