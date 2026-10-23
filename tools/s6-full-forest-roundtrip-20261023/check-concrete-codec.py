#!/usr/bin/env python3
"""Audit accepted concrete-codec source packets; never replay Lean or extraction."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for script in ['materialize-std-options.py','materialize-five-codec.py']:
 subprocess.run(['python3','-B',str(Path(__file__).with_name(script)),'--check'],check=True)
for folder in ['s6-five-codec-indent','s6-std-options-extraction']:
 root=E/folder
 for n,h in load(root/'manifest.json')['files'].items():assert sha(root/n)==h
w=E/'s6-five-codec-indent/formatter-tool';assert (w/'Translate.original.ml').read_text().replace('Format.pp_set_margin fmt 80;','Format.pp_set_margin fmt 1000;\n  Format.pp_set_max_indent fmt 999;',1)==(w/'Translate.ml').read_text()
root=E/'s6-std-options-extraction';assert not list((root/'source/generated').rglob('*External*'))
for name in ['s6-std-option-methods-charon-v1','s6-std-option-methods-aeneas-v2']:
 r=load(root/'attempts'/name/'receipt.json');assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
mat=load(E/'s6-five-codec-extraction/source-codec-materialization.json')
assert mat['unreachable_external_reference_count']==0 and len(mat['installed_actual_std_methods'])==2
assert sha(S/'S6FullSourceCodecV1.lean')==mat['source_sha256']
source=(S/'S6FullSourceCodecV1.lean').read_text();assert not re.search(r'\b(Ops|axiom|opaque|sorry|native_decide)\b',source)
assert 'Slice.Insts.CoreCmpPartialEqArray.eq' not in source
assert 'def encode (statement :' in source and 'def decode (bytes : Slice Std.U8)' in source
pins=load(E/'s6-concrete-codec-import-pins.json')
rows=load(E/'s6-concrete-codec-targets.json')['targets'];accepted=load(E/'accepted-targets.json')['targets'];reports=0
for target,attempt in rows.items():
 r=load(E/attempt/'receipt.json');assert accepted[target]['receipt']==attempt+'/receipt.json'
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(target+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(target+'.lean')).read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
core=load(E/'s6-concrete-core-freeze.json');assert core['source_freeze']=='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
blob=subprocess.check_output(['git','-C',str(R),'show',core['source_freeze']+':'+core['field_source']]);assert hashlib.sha256(blob).hexdigest()==core['field_sha256']
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,full_value_codec_no_free_children=True,snapshot_and_afterstate_reference_validators_total=True,complete_roundtrip=False,whole_codec_total=False,actual_sdk_binding=False,whole_s1_closed=False,whole_s6_closed=False)))
