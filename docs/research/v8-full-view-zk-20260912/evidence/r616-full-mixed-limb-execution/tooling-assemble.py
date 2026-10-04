from pathlib import Path
import json, hashlib, shutil

work = Path(__file__).resolve().parents[2]
bundle = Path(__file__).resolve().parent
out = bundle / 'evidence'
out.mkdir(parents=True, exist_ok=True)
leanroot = work / 'docs/research/v8-full-view-zk-20260912/lean'

# Copy each original receipt, its source snapshot, and its exact log without
# rewriting. One known interrupted run has no saved log; the manifest records it.
targets = {
    'R616': 'AspisV8R19/R616MixedLimbExecution.lean',
    'R674': 'AspisV8R19/R674TermPartition.lean',
    'R677': 'AspisV8R19/R677C1ChunkCanonical.lean',
}
attempt_rows = []
for label, target in targets.items():
    dest = out / 'attempts' / label
    dest.mkdir(parents=True, exist_ok=True)
    receipts = []
    for rp in sorted((work / '.r21-scratch').glob('aspis-focus-*.receipt.json')):
        try:
            rec = json.loads(rp.read_text())
        except Exception:
            continue
        if rec.get('target') != target:
            continue
        runid = rp.name.removeprefix('aspis-focus-').removesuffix('.receipt.json')
        ad = dest / runid
        ad.mkdir(exist_ok=True)
        entry = {'run_id': runid, 'receipt': {}, 'files': {}, 'runner_exit_status': rec.get('exit_status'),
                 'wall_time': rec.get('wall_time'), 'peak_rss_kib': rec.get('peak_rss_kib'), 'swaps': rec.get('swaps'),
                 'source_sha256': rec.get('source_sha256'), 'source_revision': rec.get('source_revision'),
                 'classification': ('compiled target successfully' if rec.get('exit_status') == 0 and rec.get('wall_time') is not None else
                                    'stopped/incomplete; wrapper status is not treated as a proof run' if rec.get('wall_time') is None else
                                    'failed compilation')}
        for srcp, dstname in [(rp, 'receipt.json'), (Path(rec.get('source_snapshot','')), 'source.lean'), (Path(rec.get('log','')), 'run.log')]:
            if srcp.exists() and srcp.is_file():
                dst = ad / dstname
                shutil.copyfile(srcp, dst)
                b = dst.read_bytes()
                entry['files'][dstname] = {'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}
            else:
                entry['files'][dstname] = {'missing': str(srcp)}
        receipts.append(entry)
    attempt_rows.append({'label': label, 'target': target, 'attempts': receipts})

# Frozen exact compiled sources for the final targets, independently pinned by receipts.
canonical_sources = []
for label, runid in [('R616','1791120408324607000'), ('R674','1791116700880133000'), ('R677','1791117409406765000')]:
    src = work / '.r21-scratch' / f'aspis-focus-{runid}.source.lean'
    recp = work / '.r21-scratch' / f'aspis-focus-{runid}.receipt.json'
    rec = json.loads(recp.read_text())
    b = src.read_bytes()
    assert hashlib.sha256(b).hexdigest() == rec['source_sha256'], (label, 'source hash mismatch')
    dest = out / 'compiled-sources' / label / Path(rec['target']).name
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dest)
    canonical_sources.append({'label':label,'path':str(dest.relative_to(bundle)), 'source_revision':rec['source_revision'],
                              'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'target':rec['target'], 'receipt_run':runid})

# Copy exact direct Lean imports of the final compiled sources; verify against the R616/R677 receipts.
deps_expected = {}
for runid in ['1791120408324607000','1791117409406765000']:
    rec = json.loads((work/'.r21-scratch'/f'aspis-focus-{runid}.receipt.json').read_text())
    deps_expected.update(rec.get('direct_local_import_sha256',{}))
dependencies=[]
for mod, expected in sorted(deps_expected.items()):
    src = leanroot / (mod.replace('.','/') + '.lean')
    if not src.is_file():
        raise FileNotFoundError(f'{mod} missing at {src}')
    b=src.read_bytes(); got=hashlib.sha256(b).hexdigest()
    if got != expected: raise ValueError(f'{mod} hash mismatch {got} != {expected}')
    dst=out/'dependency-sources'/(mod.replace('.','/')+'.lean')
    dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,dst)
    dependencies.append({'module':mod,'path':str(dst.relative_to(bundle)),'sha256':got,'bytes':len(b)})

runner = work/'.r21-scratch/run_focus.py'
shutil.copyfile(runner, out/'tooling-run_focus.py')
shutil.copyfile(Path(__file__), out/'tooling-assemble.py')

# Content hash every evidence file other than generated inventory/manifest itself.
files=[]
for p in sorted(out.rglob('*')):
    if p.is_file():
        b=p.read_bytes()
        files.append({'path':str(p.relative_to(bundle)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
manifest={'format':'Aspis R616/R674/R677 focused proof evidence v1',
          'note':'Evidence assembly only; no canonical promotion or commit. Attempts are preserved byte-for-byte.',
          'final_compiled_sources':canonical_sources,
          'direct_dependency_sources':dependencies,
          'target_attempts':attempt_rows,
          'files':files}
(bundle/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('attempt counts',[(x['label'],len(x['attempts'])) for x in attempt_rows])
print('copied evidence bytes',sum(x['bytes'] for x in files),'files',len(files))
print('manifest',bundle/'MANIFEST.json')
