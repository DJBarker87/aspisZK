#!/usr/bin/env python3
"""X7 gate (i): bodiless declarations of one RAW Aeneas emission. Every `axiom` or `opaque` declaration of the four
raw files (the two generated templates, Types.lean, Funs.lean), with its Rust path and source, classed: aspis
(source in one of the five Aspis crates, or a Rust path starting with an Aspis crate name), std (core, alloc, std,
/rustc sources), sdk (solana_* paths or sources), other. With this tool pair a function that fails to translate but
is called by a translated body becomes an axiom with exit 0, so this list, not the exit status, is the check.
Pass iff the aspis rows are exactly the write-boundary functions and runtime wrappers named in the program config,
each once, and Funs.lean contains no `sorry`. Reads only.
usage: fv_emit_bodiless.py <raw dir> <program config.json>   (TSV on stdout; last line 'gate (i) ... pass|FAIL')"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks, crate_of

R, cfg = Path(sys.argv[1]), json.loads(Path(sys.argv[2]).read_text())
expected = set(cfg['write_boundaries']) | set(cfg['runtime_wrappers'])
rows = []
for f in ('TypesExternal_Template.lean', 'Types.lean', 'FunsExternal_Template.lean', 'Funs.lean'):
    for b in blocks(R / f):
        if b['kind'] not in ('axiom', 'opaque'):
            continue
        if crate_of(b['file'], b['rust']):
            cls = 'aspis'
        elif b['rust'].startswith(('core::', 'alloc::', 'std::')) or b['file'].startswith('/rustc/'):
            cls = 'std'
        elif b['rust'].startswith('solana') or 'solana' in b['file']:
            cls = 'sdk'
        else:
            cls = 'other'
        rows.append((cls, b['kind'], b['lean'], b['rust'], f, b['decl']))
print('class\tkind\tlean_name\trust_path\tfile\tline')
for r in sorted(rows):
    print('\t'.join(map(str, r)))
aspis = [r[2] for r in rows if r[0] == 'aspis']
sorry = len(re.findall(r'\bsorry\b', (R / 'Funs.lean').read_text())) if (R / 'Funs.lean').exists() else -1
counts = {}
for r in rows:
    counts[r[0]] = counts.get(r[0], 0) + 1
ok = sorted(aspis) == sorted(expected) and sorry == 0
print('# counts ' + ' '.join('%s=%d' % kv for kv in sorted(counts.items())) + '; sorry in Funs.lean %d' % sorry)
print('# aspis bodiless: %s' % (', '.join(sorted(aspis)) or 'none'))
print('# expected: %s' % ', '.join(sorted(expected)))
extra = sorted(set(aspis) - expected)
missing = sorted(expected - set(aspis))
print('gate (i) bodiless Aspis declarations: %s%s%s' % ('pass' if ok else 'FAIL', (' unexpected: ' + ', '.join(extra)) if extra else '',
                                                       (' missing: ' + ', '.join(missing)) if missing else ''))
sys.exit(0 if ok else 1)
