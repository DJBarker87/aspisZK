#!/usr/bin/env python3
"""Offline SCB receipt/source audit; does not launch any prover or build."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipts = [json.loads((BASE / f'SCB_{i:03}' / 'receipt.json').read_text())
            for i in range(1, 8)]
assert [r['exit_status'] for r in receipts] == [1, 1, 0, 0, 0, 1, 0]
for r in receipts:
    assert r['limits'] == {'memory.high': '6442450944', 'memory.max': '8589934592',
                           'memory.swap.max': '0', 'pids.max': '64'}
    assert r['swaps'] == '0'
    assert '-M7000' in r['command']
    for name, digest in r['source_hashes'].items():
        assert sha(BASE / r['attempt'] / 'sources' / name) == digest

host = json.loads((BASE / 'SCB_HOST_SOURCES.json').read_text())
for name, digest in host.items():
    if name.startswith('S2W_'):
        local = ROOT / 'tools/s2w-20261023' / name
    else:
        local = ROOT / 'lean' / name
        if not local.exists():
            local = ROOT / 'docs/research/100bit-spend-path-20261013/lean' / name
    assert sha(local) == digest, name

for name in ['SCB_Replay', 'SCB_PhysicalRun', 'SCB_SourceReplay', 'SCB_Audit']:
    source = ROOT / 'lean' / (name + '.lean')
    assert any(r['exit_status'] == 0 and
               r['source_hashes'].get(source.name) == sha(source) for r in receipts)
    code = re.sub(r'/\-.*?\-/', '', source.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code)
    assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)', code)

audit = receipts[-1]['print_axioms']
assert len(audit) == 15
for line in audit:
    assert 'sorryAx' not in line
    names = set(re.findall(r'\[([^\]]*)\]', line)[0].split(', '))
    assert names <= {'propext', 'Classical.choice', 'Quot.sound'}
assert (BASE / 'SCB_BEFORE_Top.lean.txt').read_bytes() == (BASE / 'SCB_AFTER_Top.lean.txt').read_bytes()
assert sha(ROOT / 'lean/Rc4_Top.lean') == host['Rc4_Top.lean']
delta = json.loads((BASE / 'SCB_LEDGER_DELTA.json').read_text())
assert delta['before'] == delta['after']
ledger = json.loads((ROOT / 'evidence/recount4-20261026/Rc4_premises.json').read_text())
for scope, counts in ledger['counts'].items():
    if scope == 'all retained audit rows':
        rows = ledger['rows']
    elif scope == 'deduplicated actual plus non-alias deployment':
        rows = [r for r in ledger['rows'] if r['scope'] != 'deployment alias']
    else:
        rows = [r for r in ledger['rows'] if r['scope'] == scope]
    assert len(rows) == counts['rows']
    assert {c: sum(r['classification'] == c for r in rows) for c in ['T', 'P', 'C']} == counts['classes']
    assert delta['before'][scope] == counts
assert {r['id'] for r in delta['rows']} == {'L159', 'L185'}
assert not delta['removed'] and not delta['added']
summary = {
    'charged_lean_attempts': len(receipts), 'kani_runs': 0,
    'successful_attempts': [r['attempt'] for r in receipts if r['exit_status'] == 0],
    'excluded_failures': ['SCB_001', 'SCB_002', 'SCB_006'],
    'peak_rss_kib': max(int(r['peak_rss_kib']) for r in receipts),
    'total_wall_seconds': sum(r['wall_seconds'] for r in receipts),
    'all_swaps_zero': True, 'final_axiom_lines': len(audit),
    'actual_top_unchanged': True, 'ledger_delta': 0,
    'remaining_lean_budget_unused_due_to_explicit_stop': 93,
    'target_established': False,
}
(BASE / 'SCB_VALIDATION.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
