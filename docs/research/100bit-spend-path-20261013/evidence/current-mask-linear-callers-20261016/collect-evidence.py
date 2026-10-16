from pathlib import Path
import hashlib, json, tarfile, subprocess

w = Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015')
name = 'linear-callers'
modules = [
    'ExtractedMaskLinearStep', 'ExtractedMaskLinearLoop', 'ExtractedMaskLinears',
    'ExtractedMaskHornerCaller', 'ExtractedMaskLinearRecurrence',
    'ExtractedMaskLinearMomentBridge',
]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
files = set()
greens, attempts_all = [], []

for mod in modules:
    dirs = sorted((w/'attempts').glob('*-'+mod))
    assert dirs, f'no attempts for {mod}'
    receipts = []
    for p in dirs:
        rp = p/'receipt.json'
        assert rp.is_file(), f'missing receipt: {rp}'
        r = json.loads(rp.read_text())
        receipts.append((p, r))
        attempts_all.append({
            'module': mod, 'name': p.name, 'exit_status': r.get('exit_status'),
            'receipt_path': str(rp.relative_to(w)),
            'receipt_sha256': sha(rp),
            'source_sha256': r.get('source_sha256'),
            'wall_seconds': r.get('controller_elapsed_wall_seconds'),
            'peak_rss_kib': r.get('max_rss_kib'),
            'process_swaps': r.get('process_swaps'),
            'axiom_report_count': r.get('axiom_report_count'),
        })
        files.update(q for q in p.rglob('*') if q.is_file())
    good = [(p, r) for p, r in receipts if r.get('exit_status') == 0]
    assert len(good) == 1, (mod, [p.name for p, _ in good])
    p, r = good[0]
    src, snap, obj = Path(r['source_path']), Path(r['snapshot_path']), Path(r['output_path'])
    assert sha(src) == sha(snap) == r['source_sha256']
    assert sha(obj) == r['output_sha256']
    assert r['source_unchanged_after'] and r['process_swaps'] == 0
    assert len(r['axiom_reports']) == r['axiom_report_count'] == snap.read_text().count('#print axioms')
    assert all(set(a['axioms']) <= allowed for a in r['axiom_reports']), mod
    assert r['cgroup'] == {'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':128}
    for d in r['direct_imports']:
        assert sha(Path(d['object_path'])) == d['object_sha256'], (mod, d['module'])
    files.add(src)
    # Archive each successful module artifact and any generated companions.
    for q in [obj, Path(str(obj)+'.private'), Path(str(obj)+'.server'), obj.with_suffix('.ir')]:
        if q.is_file(): files.add(q)
    greens.append((mod, r))

manifest_source = w/'source-kit/manifest.json'
sm = json.loads(manifest_source.read_text())
for root in ['source-kit', 'evidence']:
    files.update(p for p in (w/root).rglob('*') if p.is_file())
files.update(w.glob('environment*.json'))
files.update([w/'run-mask432-one.py', w/'exec-mask432-lean.py', w/'source-kit.tar.gz'])
collector = w/'collect-mask432-linear-callers.py'
assert collector.is_file(), 'collector copy missing from remote workspace'
files.add(collector)

summary = {
    'bundle': 'aspis-r1-mask432-linear-callers-20261016',
    'scope': 'Six focused selected-mask linear recurrence/caller proof targets on Lean 4.32; not complete mask correctness or runtime refinement.',
    'source_revision': sm.get('source_revision'),
    'environment_revision': json.loads((w/'environment.json').read_text()).get('source_revision'),
    'target_count': len(greens),
    'attempt_count': len(attempts_all),
    'axiom_report_count_green_only': sum(r['axiom_report_count'] for _, r in greens),
    'green_axiom_reports_standard_only': all(set(a['axioms']) <= allowed for _, r in greens for a in r['axiom_reports']),
    'sum_controller_wall_seconds_green': round(sum(r['controller_elapsed_wall_seconds'] for _, r in greens), 3),
    'max_target_peak_rss_kib': max(r['max_rss_kib'] for _, r in greens),
    'process_swaps_green_total': sum(r['process_swaps'] for _, r in greens),
    'targets': [{
        'target': mod, 'attempt': r['attempt'], 'exit_status': r['exit_status'],
        'source_sha256': r['source_sha256'], 'snapshot_sha256': sha(Path(r['snapshot_path'])),
        'object_sha256': r['output_sha256'], 'source_path': str(Path(r['source_path']).relative_to(w)),
        'snapshot_path': str(Path(r['snapshot_path']).relative_to(w)),
        'object_path': str(Path(r['output_path']).relative_to(w)),
        'wall_seconds': r['controller_elapsed_wall_seconds'], 'peak_rss_kib': r['max_rss_kib'],
        'process_swaps': r['process_swaps'], 'axiom_report_count': r['axiom_report_count'],
        'axiom_reports': r['axiom_reports'], 'direct_imports': r['direct_imports'],
        'runner_hashes': r['runner_hashes'], 'cgroup': r['cgroup'],
    } for mod, r in greens],
    'attempts': attempts_all,
    'archived_files': [{'path':str(p.relative_to(w)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)],
}
out = w/f'{name}-summary.json'
out.write_text(json.dumps(summary, indent=2)+'\n')
files.add(out)
archive = w/f'{name}-evidence-20261016.tar.gz'
assert not archive.exists(), archive
with tarfile.open(archive, 'w:gz', compresslevel=6) as t:
    for p in sorted(files): t.add(p, arcname=str(p.relative_to(w)), recursive=False)
print(json.dumps({'summary':str(out),'summary_sha256':sha(out),'archive':str(archive),'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive),'target_count':len(greens),'attempt_count':len(attempts_all),'axiom_reports':summary['axiom_report_count_green_only']}))
