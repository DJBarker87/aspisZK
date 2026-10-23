#!/usr/bin/env python3
"""Audit focused native transition codec evidence; no release closure claim."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'s6-native-late-codec-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-native-late-codec-import-pins.json');reports=0
for target,attempt in manifest['targets'].items():
 r=load(E/attempt/'receipt.json');source=S/(target+'.lean')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 assert sha(source)==sha(E/attempt/'source.lean')==r['source_sha256']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023/factor-native-late-decoder.py'),'--check'],check=True)
subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023/split-native-late-decoder.py'),'--check'],check=True)
assert manifest['actual_native_decoder_total'] and manifest['accepted_frames_derived'] and not manifest['transition_inverse_closed'] and not manifest['whole_s6_closed']
toolpins=load(E/'s6-native-late-codec-tool-pins.json')
for path,expected in toolpins['scripts'].items():
 assert sha(R/path)==expected
source=(S/'S6NativeLateEncodeSuccessV1.lean').read_text()
assert 'theorem encode_from_decode' in source and '(accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=' in source
assert '(size : output.length=1520)' in source and '(snapshot_validated :' not in source
sourcepins=load(E/'s6-native-late-source-pins.json')
for path,hashes in sourcepins['whole_file_equal'].items():
 assert len(set(hashes.values()))==1
 for revision,expected in hashes.items():
  assert hashlib.sha256(subprocess.check_output(['git','show',revision+':'+path],cwd=R)).hexdigest()==expected
print(json.dumps(dict(targets=len(manifest['targets']),standard_or_empty_axiom_reports=reports,actual_native_decoder_total=True,accepted_frames_derived=True,accepted_encoder_success=manifest['accepted_encoder_success'],transition_inverse_closed=False,whole_s6_closed=False)))
