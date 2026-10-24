#!/usr/bin/env python3
"""Alias the complete codec carrier; retain every emitted owned operation."""
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';I=E/'s1-y1-source/owned-extraction-v3/generated/AspisS1ValuesOwned'
raw=(I/'Funs.lean.txt').read_text();s=raw.replace('import AspisS1ValuesOwned.Types','import S1ValuesOwnedTypesV1').replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
for name in ['Length','NonZeroHigh','NonCanonical']:s=s.replace('CodecError.'+name,'AspisR1CurrentCaller.compact.CodecError.'+name)
s=s.replace('end AspisS1ValuesOwned','''#print axioms read_input
#print axioms write_output
#print axioms copy_chunk
#print axioms values_owned_reference
end AspisS1ValuesOwned''')
types='''import CurrentCompactCallerTypesV1
set_option autoImplicit false
namespace AspisS1ValuesOwned
/-- Full native codec carrier: every error variant, with no projection. -/
abbrev CodecError := AspisR1CurrentCaller.compact.CodecError
#print axioms CodecError
end AspisS1ValuesOwned
'''
for n,body in [('S1ValuesOwnedTypesV1',types),('S1ValuesOwnedModelV1',s)]:
 p=S/(n+'.lean')
 if '--check' in sys.argv:assert p.read_text()==body,n
 else:p.write_text(body)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
m={'schema':'focused-extractor-proof-packet-v1','raw_funs_sha256':sha(raw),'adapted_funs_sha256':sha(s),'changes':['Import retarget to complete shared CodecError carrier','Fully qualified original codec constructors','Remove generated resource defaults','Add axiom audits'],'source_operations_unchanged':True,'opaque_operations':[],'qualification':'Complete emitted owned Vec reference, independently Kani-coupled to native on specified format call shapes. Not whole source/SDK release closure.'}
p=E/'s1-values-owned-adapter.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==m
else:p.write_text(json.dumps(m,indent=2)+'\n')
print('Owned values adapter checked' if '--check' in sys.argv else 'Owned values adapter generated')
