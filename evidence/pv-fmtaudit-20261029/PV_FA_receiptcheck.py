"""Validate completed scope receipts without changing historical evidence."""
from pathlib import Path
import hashlib, json, re, time
H = Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
rows = []
errors = []
for p in sorted(H.glob('*/receipt/receipt.json')):
    r = json.loads(p.read_text())
    d = p.parent.parent
    admission = {n: json.loads((d / n).read_text())
                 for n in ['reservation.json', 'barrier.json'] if (d / n).exists()}
    ok = len(admission) == 2 and all(v.get('allowed') is True for v in admission.values())
    lim = r['limits']
    ok = ok and lim['memory.swap.max'] == '0' and int(lim['memory.max']) <= 8 * 2**30
    if not ok:
        errors.append(d.name)
    artifact = H / ('pincompile-artifact-' + str(r.get('attempt')) + '.json')
    current_source_matches = None
    if r.get('kind') == 'pincompile' and artifact.exists():
        a = json.loads(artifact.read_text())
        src = H / 'pinned-source/backends/lean' / (a['module'] + '.lean')
        current_source_matches = hashlib.sha256(src.read_bytes()).hexdigest() == a['source_sha256'] == r['source_sha256']
        if not current_source_matches:
            errors.append('source:' + d.name)
    rows.append(dict(label=d.name, attempt=r.get('attempt'), kind=r.get('kind'),
                     exit=r['exit_status'], admission_and_caps_valid=ok,
                     pinned_source_bytes_match=current_source_matches,
                     receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
                     receipt_mtime=p.stat().st_mtime,
                     wall_seconds=r['wall_seconds'], peak_rss_kib=r['peak_rss_kib'],
                     swaps=r['swaps'], print_axioms=r.get('print_axioms')))
lean = sum(x['kind'] in ['lean', 'pincompile'] for x in rows)
native = len(rows) - lean
out = dict(time=time.time(), completed_Lean=lean, completed_native=native,
           current_native_scope_not_yet_receipted=True, errors=errors, receipts=rows)
(H / 'resume-receiptcheck.json').write_text(json.dumps(out, indent=1))
print(json.dumps(dict(Lean=lean, native=native, errors=errors)))
assert not errors
