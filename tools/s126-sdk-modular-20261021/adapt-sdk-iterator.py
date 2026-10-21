#!/usr/bin/env python3
"""Reuse only literal-equal SDK rows; retain emitted pointer and step bodies."""
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(exist_ok=True,parents=True)
t=(I/'Types.lean').read_text();f=(I/'Funs.lean').read_text()
prior=(R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/generated/AspisS2SdkOwned/Types.lean.txt').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
shared={}
for n in ['OwnedAccount','OwnedDataCell','OwnedLamportsCell','OwnedSdk']:
 pattern=lambda name:r'structure '+re.escape(name)+r' where\n([\s\S]*?)(?=\n/--|\nend )'
 a=re.search(pattern('aspis_s126_owned_sdk.'+n),t)[0].strip()
 b=re.search(pattern(n),prior)[0].strip()
 norm=lambda x:re.sub(r'\s+',' ',x.replace('aspis_s126_owned_sdk.','')).strip()
 assert norm(a)==norm(b),n
 shared[n]=dict(raw_sha256=sha(a),prior_sha256=sha(b),normalized_body_equal=True)
start=t.index('/-- [aspis_s126_sdk_iterator_reference::DataPointer]')
body=t[start:t.index('\nend AspisS2SdkIterator',start)]
# All source functions are retained. No external function templates or axioms.
f=f[f.index('/-- [aspis_s126_sdk_iterator_reference::source_begin]'):f.index('\nend AspisS2SdkIterator')]
f=f.replace('aspis_s126_owned_sdk.','AspisS2OwnedStage1.SdkReference.')
out='''import S2SdkOwnedTypesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS2SdkIterator
'''+body+'\n'+f+'\n#print axioms source_begin\n#print axioms source_next\nend AspisS2SdkIterator\n'
(O/'S2SdkSourceIteratorV1.lean').write_text(out)
(O/'sdk-iterator-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(t),raw_funs_sha256=sha((I/'Funs.lean').read_text()),source_sha256=sha(out),shared_sdk_rows=shared,changes=['reuse four literal-equal SDK structures after namespace normalization','retain both complete emitted pointer/iterator structures and both source functions','qualify the reused SDK structure names','omit generated resource-option settings'],qualification='Owned full SDK iterator reference; native source join is certified separately at the step/constructor boundary. No whole stage1 correspondence is asserted.'),indent=2)+'\n')
