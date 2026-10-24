#!/usr/bin/env python3
"""Check reused model/proof bodies and the source-version meaning of this port."""
from pathlib import Path
import subprocess,sys,importlib.util,hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
old=(B/'lean/bridge-verify-prefix-fe80-20261017/ExtractedVerifyPrefixModel.lean').read_text()
assert (S/'S1SemanticPrefixModelV1.lean').read_text()==old.replace('import ExtractedPrefixParseCore','import S1SemanticPhaseV1\nimport ExtractedPrefixParseCore',1)
old=(B/'lean/bridge-finish-a555-20261017/ExtractedVerifyFinishModel.lean').read_text()
assert (S/'S1SemanticFinishModelV1.lean').read_text()==old.replace('import ExtractedVerifyPrefixModel','import S1SemanticPrefixModelV1',1).replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
old=(B/'lean/bridge-finish-a555-20261017/ExtractedVerifyFinishReachability.lean').read_text()
assert (S/'S1SemanticFinishBoundsV1.lean').read_text()==old.replace('import ExtractedVerifyFinishModel','import S1SemanticFinishModelV1',1).replace('AspisR1PublicPreparation.FinishCalls','AspisR1PublicPreparation.S1SemanticFinishBounds')
subprocess.run([sys.executable,str(R/'tools/s1-semantic-port-20261024/generate-roots.py'),'--check'],check=True)
if '--pin-source' in sys.argv or '--check-source' in sys.argv:
 spec=importlib.util.spec_from_file_location('verify_source',R/'tools/r1-verify-migration-kit/prepare.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 sha=lambda b:hashlib.sha256(b).hexdigest()
 def declaration(raw,anchor):
  if anchor=='fn semantic_rounds<':
   first=raw.index(anchor.encode());second=raw.index(anchor.encode(),first+len(anchor));raw=raw[:second]
  return m.declaration(raw,anchor)
 revisions=['a555c852664c80000942f0c911e16719a5493625','b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a','7a40c5c2cf1135eb22f238418b802fd2d2f1fb40']
 anchors={'crates/aspis-r1-cost-probe/src/r1_semantic.rs':['pub fn public_transcript<','fn mark(','fn semantic_rounds<','fn verify_finish<','pub fn verify_observed<'],'crates/aspis-r1-cost-probe/src/r1_wire.rs':["pub fn parse(bytes:",'pub fn record(&self,','pub(crate) fn validated_record(','pub(crate) fn semantic_validated(','pub(crate) fn circle_validated(','fn sample_block_validated(','pub fn begin<']}
 rows=[]
 for path,decls in anchors.items():
  source={rev:subprocess.check_output(['git','-C',str(R),'show',rev+':'+path]) for rev in revisions}
  for anchor in decls:
   spans={rev:declaration(raw,anchor) for rev,raw in source.items()}
   assert len(set(spans.values()))==1,(path,anchor)
   assert declaration((R/path).read_bytes(),anchor)==next(iter(spans.values())),(path,anchor,'working source differs')
   rows.append({'path':path,'anchor':anchor,'declaration_sha256':sha(next(iter(spans.values()))),'identical_at':revisions})
 out={'schema':'focused-extractor-proof-packet-v1','scope':'Selected native declarations only; default/non-prover semantic_rounds is the first matching definition. This does not pin complete files as unchanged, change H5 artifact authority, or close native extraction/SDK/callee associations.','research_revision':revisions[-1],'declarations':rows}
 if '--pin-source' in sys.argv:
  (E/'s1-semantic-native-span-pins.json').write_text(json.dumps(out,indent=2)+'\n')
 else:
  assert json.loads((E/'s1-semantic-native-span-pins.json').read_text())==out,'native span pins differ'
 print(json.dumps({'unchanged_native_declarations':len(rows),'revisions':len(revisions)}))
print('Semantic model/proof source reuse checked; no resource-option override added.')
