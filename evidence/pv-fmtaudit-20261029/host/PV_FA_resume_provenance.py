"""Read-only historical trace and missing closing-object inventory."""
from pathlib import Path
import hashlib, json, os, time
H = Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
trace = []
for r in json.loads((H / 'resolution.json').read_text()):
    if not r['module'].startswith(('Aeneas/', 'AeneasMeta/')):
        continue
    p = Path(r['path'])
    candidates = [p.with_suffix('.trace')]
    if '/lib/lean/' in str(p):
        candidates.append(Path(str(p).replace('/lib/lean/', '/ir/')).with_suffix('.trace'))
    for q in candidates:
        if q.exists():
            data = q.read_bytes()
            trace.append(dict(cohort=r['cohort'], module=r['module'], path=str(q),
                              sha256=hashlib.sha256(data).hexdigest(), text=data.decode()))
missing = {'V184', 'V217', 'V218', 'V240', 'V247', 'V258', 'V259', 'V261', 'V264', 'V265'}
rows = [r for r in json.loads((H / 'claim-recorded-object-paths.json').read_text())
        if r['id'] in missing]
stems = {r['theorem'].rsplit('.', 1)[0].split('.')[-1] + '.olean': r for r in rows}
found = []
skip = {'target', 'sbf-target', 'charon-target', 'node_modules', '.git', 'source',
        'sources', 'pinned-source', 'src', 'deps'}
for job in sorted(H.parent.glob('codex-pv-*')):
    for base, dirs, files in os.walk(job):
        rel = Path(base).relative_to(job)
        dirs[:] = [d for d in dirs if d not in skip]
        if len(rel.parts) >= 9:
            dirs[:] = []
        for name in stems.keys() & set(files):
            p = Path(base) / name
            row = stems[name]
            found.append(dict(id=row['id'], theorem=row['theorem'], path=str(p),
                              sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
out = dict(time=time.time(), traces=trace, closing_object_candidates=found,
           missing_rows=sorted(missing),
           scope='Read-only Stream B directory search, depth <=9; no Stream A objects loaded')
(H / 'resume-provenance.json').write_text(json.dumps(out, indent=1))
print(json.dumps(dict(traces=len(trace), candidates=found)))
