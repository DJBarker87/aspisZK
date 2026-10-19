#!/usr/bin/env python3
"""Build cu.json from the adopted-build fixture runs and the B1 figures.
usage: collect_cu.py <host-dir> <out.json>"""
import hashlib, json, re, sys
from pathlib import Path
H = Path(sys.argv[1])
B1 = {  # design/LEAD-REVIEW-POOL-B1-20261019.md; stage 1 per proof-size cu.json b1 rows
    'transfer-13': (1199648, 1129757), 'transfer-255': (1199567, 1161066), 'transfer-1023': (1199687, 1160974),
    'withdrawal-13': (1198225, 1138950), 'withdrawal-255': (1198264, 1170523), 'withdrawal-1023': (1198386, 1170263)}
rows = []
for L, (b1s, b1t) in B1.items():
    ev = json.loads((H / 'runs/adopt' / L / 'evidence.json').read_text())
    e = ev['execution']
    rec = json.loads((H / 'receipts' / f'adopt-{L}' / 'receipt.json').read_text())
    err = (H / 'receipts' / f'adopt-{L}' / 'stderr.log').read_text()
    native = json.loads(re.search(r'FORMAT_ADOPT_NATIVE=(\{.*\})', err).group(1))
    task = H / 'runs/adopt' / L / 'task'
    proof = (task / 'r1-s2-proof.bin').read_bytes(); public = (task / 'r1-s2-public-asf8.bin').read_bytes()
    saved_public = Path('/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019/fixtures', L, 'r1-s2-public-asf8.bin').read_bytes()
    reuse = json.loads((H / 'runs/plan' / f'reuse-{L}' / 'evidence.json').read_text())['execution']
    s1, st = e['stage1_compute_units'], e['compute_units']
    rows.append({'fixture': L, 'outcome': e.get('outcome'), 'stage1_cu': s1, 'settlement_cu': st,
        'b1_stage1': b1s, 'b1_settlement': b1t, 'stage1_delta': s1 - b1s, 'settlement_delta': st - b1t,
        'stage1_ok': s1 <= b1s, 'settlement_ok': st <= b1t + 10000,
        'reuse_replay_stage1_cu': reuse['stage1_compute_units'], 'reuse_replay_settlement_cu': reuse['compute_units'],
        'proof_bytes': len(proof), 'proof_sha256': hashlib.sha256(proof).hexdigest(),
        'public_sha256': hashlib.sha256(public).hexdigest(), 'public_equal_saved_fixture': public == saved_public,
        'slot_nodes': native['slot_nodes'], 'total_nodes': native['total_nodes'], 'variable_length_bytes': native['variable_length_bytes'],
        'native_default_and_dense': [native['native_tx1_tx2_tx2_authenticated'], native['dense']],
        'receipt': {k: rec[k] for k in ['exit_status', 'wall_seconds', 'peak_rss_kib', 'swaps']}})
out = {'criterion': 'PREREG-PROOF-SIZE-2 item 1: stage 1 <= B1, settlement <= B1 + 10,000, per fixture',
       'b1_reference': 'design/LEAD-REVIEW-POOL-B1-20261019.md (settlement); proof-size-20261019/cu.json b1_stage1 (stage 1)',
       'harness': 'B1 measure driver 747cf4df patched by harness/patch_driver_adopt.py; Pool ELF 121f3e29 (cu-bound2/B1); registry as B1; LiteSVM 0.16.0; TxV1; split 10; fresh OS entropy per fixture',
       'all_stage1_ok': all(r['stage1_ok'] for r in rows), 'all_settlement_ok': all(r['settlement_ok'] for r in rows), 'rows': rows}
Path(sys.argv[2]).write_text(json.dumps(out, indent=1) + '\n')
for r in rows: print(r['fixture'], r['stage1_cu'], r['stage1_delta'], r['settlement_cu'], r['settlement_delta'], r['stage1_ok'], r['settlement_ok'], r['reuse_replay_settlement_cu'] == r['settlement_cu'])
