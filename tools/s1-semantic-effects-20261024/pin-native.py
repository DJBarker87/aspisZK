#!/usr/bin/env python3
"""Pin exact unchanged spans only; never imply a new whole-source freeze."""
from pathlib import Path
import importlib.util,subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2];spec=importlib.util.spec_from_file_location('span',R/'tools/r1-verify-migration-kit/prepare.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
p=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-semantic-effects-native-freeze.json'
if '--check' in sys.argv:latest=json.loads(p.read_text())['observed_research_revision']
else:latest=subprocess.check_output(['git','-C','/Users/dominic/ZK','rev-parse','HEAD'],text=True).strip()
revlist=['a555c852664c80000942f0c911e16719a5493625','b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a',latest]
rows=[]
for file,anchor in [('crates/aspis-r1-cost-probe/src/r1_wire.rs','pub fn new(hash: H, public_bytes:'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','fn sample_block_validated('),('crates/aspis-r1-cost-probe/src/candidate.rs','fn prepare<H: Digest32>')]:
 versions=revlist[1:] if file.endswith('candidate.rs') else revlist
 spans=[module.declaration(subprocess.check_output(['git','-C',str(R),'show',rev+':'+file]),anchor) for rev in versions];assert len(set(spans))==1,(file,anchor)
 rows.append({'file':file,'anchor':anchor,'sha256':hashlib.sha256(spans[0]).hexdigest(),'identical_at':versions})
m={'schema':'focused-extractor-proof-packet-v1','observed_research_revision':latest,'qualification':'Selected unchanged source spans, not whole SDK/artifact re-pin or closure. Reuses the previously pinned prefix/rounds/finish spans. Candidate prepare did not exist at a555 and is compared from b272 onward.','spans':rows}
if '--check' in sys.argv:assert json.loads(p.read_text())==m
else:p.write_text(json.dumps(m,indent=2)+'\n')
print('Native selected-span freeze checked')
