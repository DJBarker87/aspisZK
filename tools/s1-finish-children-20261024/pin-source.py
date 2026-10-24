#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s1-finish-selectors-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
revs=['70f8edc9d7fc9fe0e8a0bb854698419ba3a8a2f0','b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a']
files=['crates/aspis-core/src/state_only_hiding.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs']
pins={}
for path in files:
 pins[path]={rev:hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',rev+':'+path])).hexdigest() for rev in revs}
 assert len(set(pins[path].values()))==1,path
p='crates/aspis-r1-cost-probe/src/r1_semantic.rs';native={}
expressions=['core::array::from_fn(|i| claims[0][i])','core::array::from_fn(|i| claims[0][16 + i])']
for rev in revs[1:]:
 s=subprocess.check_output(['git','-C',str(R),'show',rev+':'+p],text=True)
 start=s.index('fn verify_finish<');end=s.index('\n#[inline',start);finish=s[start:end]
 assert all(finish.count(e)==1 for e in expressions)
 native[rev]=dict(file_sha256=hashlib.sha256(s.encode()).hexdigest(),finish_sha256=hashlib.sha256(finish.encode()).hexdigest())
assert len({r['finish_sha256'] for r in native.values()})==1
lib=(R/'tools/s1-finish-selectors-20261024/lib.rs').read_text()
assert all(lib.count(e)==1 for e in expressions)
model=B/'lean-candidates/query31-concrete-word-chain-20261020/sources/TerminalArrayFromFnModelV4Clean.lean'
template=B/'evidence/terminal-v4-external-model-integration-20261019/root-current-shared-mask-remainder-v3-20261019/source.lean'
old=template.read_text();old=old[old.index('/-- [aspis_r1_mask_extraction_probe'):old.index('end AspisR1SelectedMaskProbe')].strip()
copy=re.sub(r'^def ([A-Za-z0-9_.]+)',r'def sourceCopy.\1',old,flags=re.M)
new=(B/'lean-candidates/s126-caller-boundary-20261021/S1FinishMaskSourceV1.lean').read_text()
new=new[new.index('/-- [aspis_r1_mask_extraction_probe'):new.index('theorem source_body_0')].strip()
assert copy==new
source_docs=[B/'evidence/current-selected-mask-extraction-20261015/lead-review.json',B/'evidence/current-selected-mask-extraction-20261015/extraction-plan.json',template,model,B/'lean/TerminalArrayFromFnCopyEquivalenceV8.lean',B/'lean-candidates/s126-caller-boundary-20261021/S1CircleCarrierV1.lean']
(E/'source-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',adopted_revision=revs[-1],unchanged_complete_files=pins,native_selector_owner=p,native_finish=native,native_expressions=expressions,mask_body_copies=25,mask_copy_change='Only declaration names prefixed sourceCopy; 25 complete equality theorems check actual selected owner, including opaque constants.',reused_sources={str(p.relative_to(R)):sha(p) for p in source_docs},scope='Concrete source-model finish installation; native selected array expressions checked separately. S9 raw-circle/native callee, general Std/runtime, SDK/account, terminal/claims and release artifact joins remain explicit.'),indent=2)+'\n')
print(json.dumps(dict(status='PASS',unchanged_complete_native_files=len(files),mask_body_copies=25,native_selector_expressions=2)))
