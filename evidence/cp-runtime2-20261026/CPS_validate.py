#!/usr/bin/env python3
"""Read-only exact-source/receipt/axiom audit; never launches a proof."""
from pathlib import Path
import hashlib, json, re
base = Path(__file__).resolve().parent
repo = base.parent.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipts = [json.loads(p.read_text()) for p in sorted(base.glob('CPS_L*/receipt.json'))]
assert len(receipts) == 15
assert len({r['attempt'] for r in receipts}) == len(receipts)
accepted = [r for r in receipts if r['exit_status'] == 0]
failed = [r['attempt'] for r in receipts if r['exit_status'] != 0]
assert failed == ['CPS_L003', 'CPS_L009']
expected_limits = {'memory.high':'6442450944','memory.max':'8589934592',
                   'memory.swap.max':'0','pids.max':'64'}
for r in receipts:
    assert r['limits'] == expected_limits
    assert r['swaps'] == '0'
    assert '-M7000' in r['command']
    for source, digest in r['source_hashes'].items():
        assert sha(base / r['attempt'] / 'sources' / source) == digest
    reservation = json.loads((base / (r['attempt']+'-reservation.json')).read_text())
    assert reservation['allowed']
for r in accepted:
    for line in r['print_axioms']:
        match = re.search(r'depends on axioms: \[([^\]]*)\]', line)
        if match:
            assert set(match[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'}, line
modules = []
for source in sorted((repo / 'lean').glob('CPS_*.lean')):
    digest = sha(source)
    matches = [r for r in accepted if r['source_hashes'].get(source.name) == digest]
    assert matches, source
    r = matches[-1]
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s', text, re.M), source
    modules.append({'module':source.stem,'source_sha256':digest,'attempt':r['attempt']})
report = dict(lean_attempts=len(receipts),lean_successes=len(accepted),failed=failed,
              kani_runs=0,lean_remaining=100-len(receipts),kani_remaining=10,
              wall_seconds=sum(r['wall_seconds'] for r in receipts),
              max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),
              all_swaps_zero=True,all_current_sources_receipted=True,
              axioms='subset of propext, Classical.choice, Quot.sound',modules=modules,
              deployed_ledger_delta=0,target_established=False)
(base / 'CPS_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='modules'},indent=2))
