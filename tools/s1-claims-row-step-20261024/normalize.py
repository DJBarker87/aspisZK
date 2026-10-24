#!/usr/bin/env python3
"""Normalize emitted module paths/resource defaults only, never function bodies."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claims-row-step-20261024/extracted'
check='--check' in sys.argv;rows=[]
for old,new in [('Types','S1ClaimsOwnedStepTypesV1'),('Funs','S1ClaimsOwnedStepFunsV1')]:
 p=P/(old+'.lean');b=p.read_bytes();s=b.decode();s=re.sub(r'/\- You can set the `(?:maxHeartbeats|maxRecDepth)`[^\n]*\nset_option (?:maxHeartbeats|maxRecDepth) \d+\n','',s);s=s.replace('import AspisS1ClaimsOwnedStep.Types','import S1ClaimsOwnedStepTypesV1')
 if old=='Funs':s+='\n#print axioms AspisS1ClaimsOwnedStep.r1_semantic.claims_owned_step\n'
 out=D/(new+'.lean')
 if check:assert out.read_text()==s,new
 else:out.write_text(s)
 rows.append(dict(raw=old+'.lean',raw_sha256=hashlib.sha256(b).hexdigest(),maintained=str(out.relative_to(R)),maintained_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
if check:print('Normalization: PASS')
else:(P/'normalization.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',modules=rows,changes=['Remove only generated resource-option lines/advisory comments.','Rename only the Types import to the flat maintained module name.','Append #print axioms for the exact extracted owned-step body.'],namespace_unchanged=True),indent=2)+'\n')
