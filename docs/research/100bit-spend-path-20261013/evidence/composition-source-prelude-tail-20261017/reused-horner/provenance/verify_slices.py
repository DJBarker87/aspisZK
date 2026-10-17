#!/usr/bin/env python3
"""Verify exact source-byte retention of the two generated partial_fixpoint declarations."""
import hashlib, json
from pathlib import Path
SOURCE = Path('/tmp/fromfn-copy-indexed-20261016/output/generated/AspisR1SelectedMaskProbe/Funs.lean')
OUT = Path('/tmp/terminal-qm31-composition-loop-slices-v2-20261016')
SLICE = OUT / 'CompositionPartsLoopSlice.lean'
MANIFEST = OUT / 'source-manifest.json'
src = SOURCE.read_bytes()
slice_bytes = SLICE.read_bytes()
def declaration(name):
    needle = ('def pool_v1.pair_forest_semantic_terminal.' + name).encode()
    pos = src.index(needle)
    start = src.rfind(b'/--', 0, pos)
    end = src.index(b'partial_fixpoint', pos) + len(b'partial_fixpoint')
    return src[start:end].strip()
checks=[]
for name in ('composition_parts_loop0','composition_parts_loop1'):
    block = declaration(name)
    frag = (OUT / (name + '.leanfrag')).read_bytes().strip()
    # The slice contains the exact declaration block, with only outer whitespace around it.
    occurrences = slice_bytes.count(block)
    ok = block == frag and occurrences == 1
    checks.append({'name':name,'exact_bytes_equal_to_fragment':block==frag,
                   'exact_block_occurrences_in_slice':occurrences,
                   'source_block_sha256':hashlib.sha256(block).hexdigest(),
                   'fragment_sha256':hashlib.sha256(frag).hexdigest(),'ok':ok})
result={'candidate_funs_path':str(SOURCE),'candidate_funs_sha256':hashlib.sha256(src).hexdigest(),
        'slice_path':str(SLICE),'slice_sha256':hashlib.sha256(slice_bytes).hexdigest(),
        'comparison':'exact declaration bytes; only leading/trailing whitespace stripped; no renaming or internal normalization',
        'checks':checks,'all_ok':all(c['ok'] for c in checks)}
(OUT/'slice-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if not result['all_ok']: raise SystemExit(1)
