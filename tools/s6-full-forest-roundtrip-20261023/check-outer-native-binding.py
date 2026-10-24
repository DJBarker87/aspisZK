#!/usr/bin/env python3
"""Audit focused native transition codec evidence; no release closure claim."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'s6-outer-native-binding-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-outer-native-binding-import-pins.json');reports=0
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
for script in ['materialize.py','materialize-named-encoder.py','generate-outer-carrier-bridge.py']:
 subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023'/script),'--check'],check=True)
assert manifest['full_carrier_bijections']==15 and manifest['concrete_children']==5 and not manifest['free_ops_parameter']
assert not manifest['outer_encoder_total'] and not manifest['outer_inverse'] and not manifest['current_sdk_binding'] and not manifest['whole_s6_closed']
installed=(S/'S6OuterNativeInstalledV1.lean').read_text()
assert 'def encode (statement : Statement)' in installed and 'nativeOps (fromPoolV1PairForestTerminalStatementV1 statement)' in installed
assert '(ops :' not in installed
ops=(S/'S6OuterNativeOpsV1.lean').read_text();assert 'def nativeOps :' in ops
for field in ['digest','validate','withdrawal','transfer','late']:assert '  '+field+' :=' in ops
returns=(S/'S6OuterNativeReturnsV1.lean').read_text()
for field in ['validate','withdrawal','transfer','late']:assert 'theorem '+field+'_return' in returns
for path,expected in load(E/'s6-outer-native-binding-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
import runpy
functions=runpy.run_path(str(R/'tools/s6-full-forest-roundtrip-20261023/check-native-parent-source-pins.py'))['functions']
source=load(E/'s6-outer-native-binding-source-pins.json')
texts={revision:subprocess.check_output(['git','show',revision+':'+source['file']],cwd=R,text=True) for revision in source['file_sha256']}
for revision,text in texts.items():assert hashlib.sha256(text.encode()).hexdigest()==source['file_sha256'][revision]
for name,hashes in source['byte_equal_function_spans'].items():
 for revision,expected in hashes.items():assert [hashlib.sha256(x.encode()).hexdigest() for x in functions(texts[revision],name)]==expected
for name,hashes in source['byte_equal_original_module_constants'].items():
 pattern=r'(?m)^(?:pub(?:\([^)]*\))?\s+)?const\s+'+name+r'\b[\s\S]*?;[ \t]*(?:\n|$)'
 for revision,expected in hashes.items():assert hashlib.sha256(re.search(pattern,texts[revision])[0].encode()).hexdigest()==expected
print(json.dumps(dict(targets=len(manifest['targets']),standard_or_empty_axiom_reports=reports,full_carrier_bijections=15,concrete_children=5,free_ops_parameter=False,outer_encoder_total=False,outer_inverse=False,whole_s6_closed=False)))
