#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

P = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
raw_t = (P/'generated/raw/Types.lean').read_text()
raw_f = (P/'generated/raw/Funs.lean').read_text()
clean = lambda s: re.sub(r'^set_option maxRecDepth 2048\n|^set_option maxHeartbeats 1000000\n', '', s, flags=re.M)
want_t = clean(raw_t)
marker = """/-- [aspis_r1_stage2_adopted_resume::verifier::Error]
    Source: 'lib.rs', lines 870:0-870:88
    Visibility: public -/
@[discriminant isize]
inductive verifier.Error where"""
replacement = marker.replace("@[discriminant isize]\n", "")
assert want_t.count(marker) == 1
want_t = want_t.replace(marker, replacement, 1)
got_t = (P/'SuffixTypes-discriminant-adjusted.lean').read_text()
got_f = (P/'SuffixFuns-resource-options-stripped.lean').read_text()
assert got_t == want_t
assert got_f == clean(raw_f)
assert "@[discriminant isize]\ninductive verifier.Error" not in got_t
assert "@[discriminant isize]\ninductive transport.Variant" in got_t
receipt = json.loads((P/'native/bridge-v3/receipt.json').read_text())
assert receipt['exit_status'] == 0
assert receipt['output_sha256'] == json.loads((P/'dependency-pins.json').read_text())['green_objects']['PrefixSuffixAlphaBridge']
assert receipt['source_sha256'] == sha((P/'PrefixSuffixAlphaBridge.lean').read_bytes())
print(json.dumps({
  'status':'pass',
  'raw_types_sha256':sha(raw_t.encode()),
  'adjusted_types_sha256':sha(got_t.encode()),
  'raw_funs_sha256':sha(raw_f.encode()),
  'adjusted_funs_sha256':sha(got_f.encode()),
  'types_change':'generated resource-option lines stripped; exactly one verifier.Error discriminant annotation removed',
  'funs_change':'generated resource-option lines stripped only',
  'green_receipt_output':receipt['output_sha256']
},indent=2))
