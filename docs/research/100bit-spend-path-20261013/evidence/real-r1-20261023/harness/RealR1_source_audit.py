#!/usr/bin/env python3
"""Check reuse against actual historical source, without rebuilding artifacts."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent
ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())

def function(text, name):
    start = re.search(r'\bfn ' + re.escape(name) + r'\s*\(', text).start()
    left = text.index('{', start)
    depth, end = 1, left + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end]

rows = []
for revision, path, names in [
    ('0583e6bd56e65e7a13aa91426610c4357d9940eb',
     'crates/aspis-r1-cost-probe/src/prover.rs',
     ['prove_masked_retrying_with', 'prove_masked_attempt', 'prove_masked_with_attempt', 'mask_error']),
    ('5296bb1e509fdd32ec3cbb4fc70f640db071e7c7',
     'crates/aspis-prover/src/state_only_entropy.rs',
     ['generate_for_mask_nonce', 'reserve_and_build_pool_v1_pair_forest_mask_material_v1',
      'reservation_path', 'reserve_fallible']),
]:
    old = subprocess.check_output(['git', 'show', revision + ':' + path], text=True)
    now = (ROOT / path).read_text()
    for name in names:
        a, b = function(old, name), function(now, name)
        assert a == b, (path, name, 'source changed; historical gate cannot transfer')
        rows.append(dict(path=path, function=name, historical_revision=revision,
                         verbatim_equal=True, bytes=len(b.encode()),
                         sha256=hashlib.sha256(b.encode()).hexdigest()))
    if path.endswith('prover.rs'):
        assert 'constATTEMPT_CAP:usize=8;' in now.replace(' ', '')
    else:
        assert re.search(r'const ENTROPY_RETRY_LIMIT: usize = 16;', now)

record = dict(source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
              functions=rows,
              native_boundary='P6 source mapping and verified primitive substitutions; no Rust syntax theorem',
              selected_route='public adversary-chosen nonce; 64-byte draw; S2; eight attempts',
              exclusions=['sim.rs', '96-byte generate()', 'unadopted CT v2 changes'],
              reused_gates=['part34 retry-eight-v2 and entropy-rejected-aborts',
                            'part43 candidate-full-bytes-error-payload-v2',
                            'part42/43 selected-owner induction and model bridge'])
(OUT / 'source-identity.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(identical_functions=len(rows), source_revision=record['source_revision'])))
