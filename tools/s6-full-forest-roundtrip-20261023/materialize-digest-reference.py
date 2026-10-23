#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
raw=B/'lean/AspisR1PairForestLaneEncoderTailSourceCut/Funs.lean';f=clean(raw.read_text())
ms=list(re.finditer(r'(?m)^def\s+([^\s(:]+)',f));blocks={}
for i,m in enumerate(ms):
 end=ms[i+1].start() if i+1<len(ms) else f.index('\nend AspisR1PairForestLaneEncoderTailSourceCut',m.end())
 blocks[m[1]]=f[m.start():end]
body='\n'.join(blocks[x] for x in ['M31.to_le_bytes','encode_digest_canonical'])
text='''import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS6DigestReference
abbrev M31 := U32
'''+body+'''
#print axioms encode_digest_canonical
end AspisS6DigestReference
'''
p=S/'S6DigestReferenceV1.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
source=B/'evidence/pair-forest-lane-encoder-extraction-20261017/input/lib.rs';rust=source.read_text();a=rust.index('pub fn encode_digest_canonical(');b=rust.index('\n}',a)+2;old=rust[a:b]
reference=json.loads((E/'s6-full-forest-native/digest-encoder/input/source-manifest.json').read_text())['reference']
normalized=old.removeprefix('pub ').replace('encode_digest_canonical','reference')
for x,y in [('digest','d'),('bytes','b')]:normalized=re.sub(r'\b'+x+r'\b',y,normalized)
assert re.sub(r'\s+','',normalized)==re.sub(r'\s+','',reference)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=dict(schema='focused-extractor-proof-packet-v1',raw_source=str(raw.relative_to(R)),raw_sha256=sha(raw),rust_source=str(source.relative_to(R)),rust_sha256=sha(source),candidate_sha256=sha(p),native_reference_exact_after_function_publicity_and_identifier_alpha_renaming=True,native_predecessor='s6-native-digest-encoder-v2',qualification='Retain exactly the complete eight-limb/32-byte reference and M31 byte method from existing extraction; namespace only changes, metadata/comments/options removed. Full digest carrier retained as native unsigned-word model. Native frozen loop equality checked separately. No whole forest/native runtime closure.')
p=E/'s6-digest-reference-materialization.json';encoded=json.dumps(meta,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==encoded
else:p.write_text(encoded)
