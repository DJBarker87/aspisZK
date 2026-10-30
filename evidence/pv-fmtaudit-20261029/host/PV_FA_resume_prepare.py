"""Prepare supplementary comparisons and V261 forensic footprint, capped."""
from pathlib import Path
import hashlib, json
H = Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
fresh = {}
for p in sorted(H.glob('pincompile-artifact-*.json')):
    a = json.loads(p.read_text())
    if a['exit_status'] == 0 and '--root=' in ' '.join(a['command']):
        fresh[a['module']] = a
res = {(r['cohort'], r['module']): r for r in json.loads((H/'resolution.json').read_text())}
lines = []
for mod, a in sorted(fresh.items()):
    left = H / 'pinned-objects' / (mod + '.olean')
    assert hashlib.sha256(left.read_bytes()).hexdigest() == a['output_sha256']
    for cohort in ['b3q', 'event', 'ndr', 'authority']:
        r = res[cohort, mod]
        assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest() == r['sha256']
        lines.append('\t'.join([cohort + '-fresh-source', mod, str(left), r['path']]))
(H/'resume-object-pairs.tsv').write_text('\n'.join(lines)+'\n')
provenance = json.loads((H/'resume-provenance.json').read_text())
footprints = []
selection = []
for r in provenance['closing_object_candidates']:
    p = Path(r['path'])
    rel = r['theorem'].rsplit('.',1)[0].replace('.','/')+'.olean'
    root = Path(str(p)[:-len(rel)])
    for ep in [root.parent/'env-J-private.json', root.parent/'env-J.json',
               root.parent/'J.json', root.parent/'env/J.json']:
        if not ep.exists():
            continue
        e = json.loads(ep.read_text())
        if not e.get('LEAN_PATH'):
            continue
        roots = list(dict.fromkeys([str(root)] + e['LEAN_PATH'].split(':')))
        selection.append(dict(**r, env=str(ep), roots=roots,
                              status='forensic variant; no recorded closure SHA assertion'))
        footprints.append('\t'.join([r['id'],r['theorem'],':'.join(roots)]))
        break
(H/'resume-footprint-inputs.tsv').write_text('\n'.join(footprints)+'\n')
(H/'resume-fresh-selection.json').write_text(json.dumps(dict(fresh=fresh, footprint_selection=selection),indent=1))
print('Fresh source modules',len(fresh),'comparisons',len(lines),'footprints',len(footprints))
# Recheck the original cohort fingerprints and archive all new preflights.
exec((H/'PV_FA_post.py').read_text())
