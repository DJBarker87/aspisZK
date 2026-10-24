#!/usr/bin/env python3
"""Audit focused native transition codec evidence; no release closure claim."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'s6-native-forest-decoder-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-native-forest-decoder-import-pins.json');reports=0
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
assert manifest['actual_native_decoder_total'] and manifest['accepted_frames_derived'] and manifest['common_prefix_bytes']==144
assert not manifest['outer_inverse'] and not manifest['current_sdk_binding'] and not manifest['whole_s6_closed']
source=(S/'S6NativeForestDecodeTotalV1.lean').read_text()
assert 'theorem decode_total (bytes : Slice U8)' in source and '∃ result,decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok result' in source
source=(S/'S6NativeForestAcceptedFramesV1.lean').read_text()
assert '(accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=' in source and '(ops :' not in source
for path,expected in load(E/'s6-native-forest-decoder-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
import runpy
functions=runpy.run_path(str(R/'tools/s6-full-forest-roundtrip-20261023/check-native-parent-source-pins.py'))['functions']
pins=load(E/'s6-native-forest-decoder-source-pins.json')
texts={revision:subprocess.check_output(['git','show',revision+':'+pins['file']],cwd=R,text=True) for revision in pins['file_sha256']}
for revision,text in texts.items():assert hashlib.sha256(text.encode()).hexdigest()==pins['file_sha256'][revision]
for name,hashes in pins['byte_equal_function_spans'].items():
 for revision,expected in hashes.items():assert [hashlib.sha256(v.encode()).hexdigest() for v in functions(texts[revision],name)]==expected
print(json.dumps(dict(targets=len(manifest['targets']),standard_or_empty_axiom_reports=reports,actual_native_decoder_total=True,accepted_frames_derived=True,common_prefix_bytes=144,outer_inverse=False,whole_s6_closed=False)))
