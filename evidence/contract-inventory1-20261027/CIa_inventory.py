"""Offline documentation inventory; no Lean execution or contract mutation."""
import csv
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / 'evidence/l188-audit1-20261027'
OUT = Path(__file__).resolve().parent
DOC = ROOT / 'design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md'
fields = json.loads((AUDIT / 'L8a_TrustFieldMap.json').read_text())
surfaces = json.loads((AUDIT / 'L8a_SurfaceClassification.json').read_text())
assert len(fields) == len({r['field'] for r in fields}) == 44
assert len(surfaces) == len({r['name'] for r in surfaces}) == 9224
rows = ['| Exact projection (one row per field) | Contract item now | Status | Dated authority / limit |',
        '|---|---|---|---|']
for r in sorted(fields, key=lambda x: x['field']):
    historical = r['item'] == 'historical checkpoint interface'
    status = ('NAMED-IN-CONTRACT' if r['contract_literal_name_present'] else
              'ACCEPTED-ELSEWHERE†' if historical else 'ACCEPTED-ELSEWHERE')
    current = r['item'] + ' (§3, 2026-10-26)' if r['contract_literal_name_present'] else 'No literal item; ' + r['item']
    authority = r['acceptance']
    if historical:
        authority = 'TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust'
    elif authority.startswith('same std'):
        authority = 'LOG D157 2026-10-22 08:35; C3-BIN 2026-10-23 18:05 and 2026-10-25 late'
    elif r['item'] == 'AeneasExtraction':
        authority += '; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26'
    elif r['item'] == 'S2TrustedSdkBorrow':
        authority += ' (D189 2026-10-23 17:35)'
    rows.append(f"| `{r['field']}` | {current} | **{status}** | {authority}; {r['scope']} |")
text = DOC.read_text()
if '<!-- CIa_FIELD_TABLE -->' in text:
    DOC.write_text(text.replace('<!-- CIa_FIELD_TABLE -->', '\n'.join(rows)))
# Every imported nonstandard axiom remains an individual UNRECORDED finding.
# No import-only implementation flag is reclassified as a security premise.
with (OUT / 'CIa_UnrecordedAxioms.tsv').open('w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n')
    w.writerow(['declaration', 'status', 'Rc10_import', 'ARX_import', 'Rc10_reachable', 'ARX_reachable', 'scope'])
    for r in sorted(surfaces, key=lambda x: x['name']):
        if r['classification'].startswith('F-AXIOM:'):
            w.writerow([r['name'], 'UNRECORDED', *r['import_roots'], *r['reachable_roots'], r['classification']])
print(json.dumps({'named_fields': len(fields), 'named_items': dict(Counter(r['item'] for r in fields)),
                  'declaration_surfaces': len(surfaces),
                  'surface_classes': dict(Counter(r['classification'] for r in surfaces))}, indent=2))
