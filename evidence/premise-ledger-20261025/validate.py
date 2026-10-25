"""Check this static audit's receipts, source snapshots, field coverage and totals."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import ledger

root, out = ledger.ROOT, ledger.OUT
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
doc = root/'design/PREMISE-LEDGER-20261025.md'
old = doc.read_bytes()
ledger.render()
assert doc.read_bytes() == old, 'ledger rendering changed; review generated document'
data = json.loads((out/'premises.json').read_text())
assert len(data['rows']) == len(set(r['name'] for r in data['rows']))
assert {r['classification'] for r in data['rows']} == {'T','P','C'}
assert {r['owner'] for r in data['rows']} == {'lead','session A','external'}
for row in data['rows']:
    for definition in row['definition'].split('; '):
        file = definition.split('#')[0]
        assert (root/file).is_file(), (row['name'], file)
    assert all(row[k] for k in ['definition','meaning','job','evidence'])

attempts = []
for i in range(1,8):
    d = out/f'Ledger_{i:03}'
    r = json.loads((d/'receipt.json').read_text())
    assert r['exit_status'] == (1 if i < 3 else 0)
    assert r['limits'] == {'memory.high':'6442450944','memory.max':'8589934592',
                            'memory.swap.max':'0','pids.max':'64'}
    assert r['swaps'] == '0'
    assert '-M7000' in r['command']
    assert r['source_revision'] == 'a8f85a1c67'
    for name, expected in r['source_hashes'].items():
        assert sha(d/'sources'/name) == expected
        if i >= 3:
            assert sha(root/'lean'/name) == expected
            s = (root/'lean'/name).read_text()
            assert not re.search(r'^\s*(?:theorem|lemma|axiom|def|instance)\b', s, re.M)
    for line in r['print_axioms']:
        axioms = set(re.findall(r'(?:propext|Classical\.choice|Quot\.sound)', line))
        assert axioms == {'propext','Classical.choice','Quot.sound'}
        assert 'sorryAx' not in line
    if i < 3:
        errors = [s for s in (d/'stdout.log').read_text().splitlines() if ': error:' in s]
        assert errors == [f'{r["sources"][0]}:7:0: error: Unknown option `pp.width`']
    attempts.append({k:r[k] for k in ['attempt','command','source_revision','source_hashes',
        'deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})

# Inventory named fields from the successful kernel pretty printer output,
# before each constructor repetition. Exact dependent types remain in logs.
catalog = {}
for i in [3,4,5,6,7]:
    s = (out/f'Ledger_{i:03}'/'stdout.log').read_text()
    blocks = re.split(r'(?=^structure )',s,flags=re.M)
    for block in blocks:
        if not block.startswith('structure '):
            continue
        name = re.match(r'structure (\S+)',block)[1]
        fields = block.split('fields:\n',1)[1].split('constructor:',1)[0]
        catalog[name] = dict(attempt=f'Ledger_{i:03}',fields=fields,
            field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
assert len(catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names']) == 15
assert len(catalog['FS2.Duplex.Params']['field_names']) == 10
assert len(catalog['AspisR1.Port4D_Pairing.PairingLaws']['field_names']) == 6
names = [r['name'] for r in data['rows']]
for name in catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names']:
    field = name.rsplit('.',1)[-1]
    assert any(n.startswith('sdk.'+field+'.') for n in names), field
for prefix,fields in {
    'writer.':['header','size'], 'reader.':['checkedHeader'],
    'history.':['savedAtCommit','loadedAtEntry','noInterveningWrite'],
    'P6Boundary.':['oracle','binary_parent','occupied_parent','sibling_parent','leaf'],
    'r0.':['field0','field4','add','quarter_run','multiply','evaluate'],
    'r1.':['field0','field4','add','quarter_run','multiply','evaluate'],
    'pairing_S3_S5_S9.':['claim','alpha0','alpha1','pair'],
}.items():
    for field in fields:
        assert prefix+field in names, (prefix,field)
(out/'printed-field-catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')

reused = [
    'evidence/op4-p6-20261025/Op4P_lean013/receipt.json',
    'evidence/tx2-install-20261025/Tx2I-006/receipt.json',
    'evidence/ports1-20261023/lean-016/receipt.json',
    'docs/research/100bit-spend-path-20261013/evidence/dv-twotx-20261021/OraclePortHeadlineFrozen2PerAttempt-1/receipt.json',
    'evidence/op5-concrete-20261025/HANDOFF.md',
    'evidence/tx2-query-20261025/HANDOFF.md',
    'design/SOUND-INT-20261025.md',
]
pins = []
for p in reused:
    assert (root/p).is_file(), p
    pins.append(dict(path=p, sha256=sha(root/p)))
source_matches = []
for file, receipt in [
    ('lean/Op4P_Accepted.lean',reused[0]),
    ('lean/Tx2I_Accepted.lean',reused[1]),
    ('docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalHeadline.lean',reused[2]),
    ('docs/research/100bit-spend-path-20261013/lean/OraclePortHeadlineFrozen2PerAttempt.lean',reused[3]),
]:
    r = json.loads((root/receipt).read_text())
    digest = r.get('source_sha256') or r['source_hashes'][Path(file).name]
    assert sha(root/file) == digest, file
    source_matches.append(dict(path=file,sha256=digest,checked_receipt=receipt))
    if 'object_sha256' in r:
        assert attempts[3]['deps_fingerprint']['selected_objects']['OraclePortHeadlineFrozen2PerAttempt.olean']['sha256'] == r['object_sha256']
summary = dict(kind='Signature/field audit only; no new theorem or closure',
    source_revision_anchor_full=subprocess.check_output(['git','rev-parse','a8f85a1c67'],cwd=root,text=True).strip(),
    budget=dict(lean_used=7,lean_limit=15,kani_used=0,kani_limit=0),
    counts=data['counts'],owners=data['owners'],attempts=attempts,reused_pins=pins,source_matches=source_matches,
    checks=['rows unique; classes/owners valid; definition files exist',
        'current helper hashes match successful recorded sources',
        '15 SDK fields, FS2 Params and nested finish/history/P6 fields exposed',
        'all accepted endpoint axiom reports exactly standard three',
        'all scopes exact requested caps, zero swaps; no new declarations',
        'generated document and JSON agree'])
(out/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(rows=len(names), counts=data['counts'],lean=7,kani=0,checked=True),indent=2))
