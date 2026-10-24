#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
R = Path(__file__).resolve().parents[2]
B = R/'docs/research/100bit-spend-path-20261013'
E = B/'evidence/s126-current-caller-20261021'
S = B/'lean-candidates/s126-caller-boundary-20261021'
P = E/'s1-semantic-fold-controls-20261024'
names = {
    'S1ExtractedRoundChildrenV1':'s1-extracted-round-children-v1',
    'S1ExtractedRoundChildrenTotalV1':'s1-extracted-round-children-total-v1',
    'S1TopPrepareExtractedChildrenV1':'s1-top-prepare-extracted-children-v1',
    'S1OwnedStage1ExtractedChildrenV1':'s1-owned-stage1-extracted-children-v2',
}
sha = lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((E/'accepted-targets.json').read_text())
receipts = []
for name,attempt in names.items():
    r = json.loads((E/attempt/'receipt.json').read_text())
    assert r['exit_status'] == 0 and r['target'] == name
    assert sha(S/(name+'.lean')) == sha(E/attempt/'source.lean') == r['source_sha256']
    assert r['swaps'] == 0 and r['print_axioms']
    assert all('sorryAx' not in s for s in r['print_axioms'])
    m['targets'][name] = {k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']}
    m['targets'][name]['receipt'] = attempt+'/receipt.json'
    receipts.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics = dict(targets=len(names),wall_seconds=sum(r['wall_seconds'] for r in receipts),
    max_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts))
(P/'lean-targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    targets=names,metrics=metrics,qualification='Concrete extracted round-child installation at same accepted op7 and owned stage1; canonical-domain TOTAL helper theorems. Not native SDK/Std/abort or global security closure.'),indent=2)+'\n')
(P/'tool-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    files={str(p.relative_to(R)):sha(p) for p in sorted((R/'tools/s1-semantic-fold-20261024').glob('*')) if p.is_file()},
    reused_runner={str(R/'tools/s126-sdk-20261021/lean-local.py'):sha(R/'tools/s126-sdk-20261021/lean-local.py')}),indent=2)+'\n')
print(json.dumps(metrics))
