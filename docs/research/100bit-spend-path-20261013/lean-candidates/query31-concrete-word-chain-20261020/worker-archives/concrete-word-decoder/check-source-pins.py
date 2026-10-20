#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
W=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
# The resource-clean standard model is exactly the accepted V4 source minus
# its two resource-control options; no term or proof body may change.
original=(W/'references/TerminalArrayFromFnModelV4Original.lean').read_text()
clean=(W/'sources/TerminalArrayFromFnModelV4Clean.lean').read_text()
expected=original.replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
assert clean==expected
# Confirm the Rust span pins against the archived full source.
rust=(W/'references/r0_transcript.rs').read_bytes()
pins=json.loads((W/'references/QueryScanSourcePins.reference.json').read_text())
for name in ('query_bound','block_rank','query_words'):
    pin=next(x for x in pins['cuts'] if x['name']==name)
    body=rust[pin['start_byte']:pin['end_byte_exclusive']]
    assert sha(body)==pin['sha256'], name
    assert pin['source_file_sha256']==sha(rust), name
# Accepted Lean owners must not import generated Funs/FunsExternal or introduce
# resource-control options/custom axioms/native_decide.
for rel in ('sources/QueryScanConcreteWordsDecoder.lean',
            'sources/Query31ConcreteWordsDriverChain.lean',
            'sources/TerminalArrayFromFnModelV4Clean.lean'):
    t=(W/rel).read_text()
    assert 'import AspisR1QueryScan.Funs' not in t
    assert 'import AspisR1QueryScan.FunsExternal' not in t
    assert 'set_option maxHeartbeats' not in t and 'set_option maxRecDepth' not in t
    assert 'native_decide' not in t
    assert '\naxiom ' not in t
print('source pins and option-only clean diff: PASS')
