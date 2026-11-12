#!/usr/bin/env python3
"""X2: assemble the published tables from the per-run tables (reads only; writes only <out dir>).
rows.tsv = the rows of the overflow-off run (the deployed setting) followed by the rows of the overflow-on run, each
with its setting in the overflow_checks column; plus, for both settings, one row per Aspis function that is
reachable from the entry and has no doc block in the package: the function whose signature Aeneas cannot translate,
and the library-crate functions not emitted by the tool (from not-emitted.tsv, reason "dropped by the tool").
usage: fv_x2_assemble.py <tables-off> <tables-on> <gaps.json> <bodyhash-frozen.json> <bodyhash-pin.json> <out dir>"""
import csv, json, sys
from pathlib import Path
OFF, ON, GAPS, BHF, BHP, OUT = Path(sys.argv[1]), Path(sys.argv[2]), json.load(open(sys.argv[3])), json.load(open(sys.argv[4])), json.load(open(sys.argv[5])), Path(sys.argv[6])
rd = lambda p: list(csv.DictReader(open(p), delimiter='\t'))
off, on = rd(OFF / 'rows.tsv'), rd(ON / 'rows.tsv'); cols = list(off[0].keys())
bykey = {}
for f in BHF['functions']: bykey.setdefault((f['path'], f['name']), []).append(f)
pin = {}
for f in BHP['functions']: pin.setdefault(f['key'], []).append(f['body_sha256'])
def extra(path, crate, file, name, translates, note, ovf):
    c = bykey.get((file, name), [])
    b = c[0] if len(c) == 1 else None
    ch = '' if not b else ('new (absent at the pin)' if b['key'] not in pin else 'unchanged' if b['body_sha256'] in pin[b['key']] else 'changed')
    return dict(rust_path=path, crate=crate, file_line='%s:%s' % (file, b['start'] if b else ''), source_revision=BHF['revision'], body_sha256=b['body_sha256'] if b else '',
                ledger_key=b['key'] if b else '', translates=translates, elaborates='not run (not translated)', lean_module='', lean_name='', overflow_checks=ovf,
                changed_vs_pin_c7593d23fdc=ch, lean_error_class='', note=note)
add = []
g = GAPS['aspis_pool::pair_forest::process_pair_forest_terminal_with_verifier_v1']
add.append(('aspis_pool::pair_forest::process_pair_forest_terminal_with_verifier_v1', 'aspis_pool', 'programs/aspis-pool/src/pair_forest.rs', 'process_pair_forest_terminal_with_verifier_v1',
            'no: signature not translatable (opaque by name; no declaration emitted)', 'named gap: ' + g['message'] + ' | construct: ' + g['construct']))
for r in rd(OFF / 'not-emitted.tsv'):
    if not r['reason'].startswith('dropped by the tool'): continue
    file = ('crates/aspis-statement/src/' if r['crate'] == 'aspis_statement' else 'crates/aspis-core/src/' if r['crate'] == 'aspis_core' else 'programs/aspis-pool/src/') + r['file_line'].split(':')[0]
    add.append((r['function'], r['crate'], file, r['function'].split('::')[-1], 'no: not emitted (dropped by the tool)', r['reason']))
rows = [dict(x) for x in off] + [extra(*a, 'off') for a in add] + [dict(x) for x in on] + [extra(*a, 'on') for a in add]
OUT.mkdir(parents=True, exist_ok=True)
with open(OUT / 'rows.tsv', 'w') as f:
    f.write('\t'.join(cols) + '\n')
    for r in rows: f.write('\t'.join(r.get(k, '') for k in cols) + '\n')
import collections
t = collections.Counter()
for r in rows:
    cat = ('translates and elaborates' if r['elaborates'] == 'yes' else 'translates only') if r['translates'] == 'yes' else ('named gap' if 'named gap' in r['translates'] or 'signature' in r['translates'] else 'not translated')
    t[(r['overflow_checks'], r['crate'], cat)] += 1; t[(r['overflow_checks'], 'all', cat)] += 1
for k in sorted(t): print(k, t[k])
