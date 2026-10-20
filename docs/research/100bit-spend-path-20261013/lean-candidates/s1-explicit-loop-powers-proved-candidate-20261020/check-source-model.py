#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
R=next(x for x in D.parents if (x/'.git').exists())
P=R/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'extraction-input/source-pins.json').read_text())
for f,h in pins['kit_files'].items():assert sha((D/'extraction-input'/f).read_bytes())==h,f
new=(D/'extraction-input/lib.rs').read_text();transform=pins['candidate_transform']
assert new.count(transform['after'])==1
old=new.replace(transform['after'],transform['before'],1)
assert old==(P/'evidence/s1-current-powers-callback-20261020/extraction-input/lib.rs').read_text()
for cut in pins['cuts']:
 original=subprocess.check_output(['git','-C',str(R),'show',pins['revision']+':'+cut['path']])
 frozen=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+cut['path']])
 assert original==frozen,cut['path']
 assert sha(original)==cut['file_sha256']
 assert sha(original[cut['start_byte']:cut['end_byte_exclusive']])==cut['sha256']
def body(f):
 text=f.read_text();return text.split('namespace AspisR1LoopPowers\n',1)[1].rsplit('end AspisR1LoopPowers',1)[0]
model=(D/'sources/LoopPowersCandidateModel.lean').read_text()
for f in ['Types.lean','Funs.lean']:
 chunk=body(D/'diagnostics/raw-generated/AspisR1LoopPowers'/f)
 assert model.count(chunk)==1,f
assert 'axiom ' not in model and 'sorry' not in model
assert 'def field.WideExact.mul' not in (D/'diagnostics/raw-generated/AspisR1LoopPowers/Funs.lean').read_text()
assert 'axiom field.WideExact.mul' in (D/'diagnostics/raw-generated/AspisR1LoopPowers/FunsExternal_Template.lean').read_text()
np=json.loads((D/'native/source-pins.json').read_text())
assert sha((D/'native/input/main.rs').read_bytes())==np['main_sha256']
for f in np['files']:
 assert sha(subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+f['path']]))==f['sha256']
samples=json.loads((D/'native/sample-inputs.json').read_text())
assert len(samples)==268 and all(len(a)==8 and all(0<=v<2147483647 for v in a) for a in samples)
print(json.dumps({'status':'PASS','production_source_unchanged':'b2727acd3','source_cuts':len(pins['cuts']),'raw_types_and_all_function_bodies':'exact retained substrings','native_canonical_samples':len(samples),'scope':'CANDIDATE explicit loop, not adopted frozen powers'},indent=2))
