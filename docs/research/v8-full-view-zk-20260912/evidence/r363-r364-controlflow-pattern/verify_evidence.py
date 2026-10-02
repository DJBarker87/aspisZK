#!/usr/bin/env python3
"""Verify the portable R363/R364 diagnostic evidence package without running tools."""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

files={p.relative_to(ROOT).as_posix():p for p in ROOT.rglob('*') if p.is_file() and p != ROOT/'SHA256SUMS'}
assert not any(p.is_symlink() for p in ROOT.rglob('*')), 'unexpected symlink'
forbidden=('.olean','.ilean','.cmi','.cmo','.cmx','.o','.a','.pyc','.exe')
for name in files:
    assert not name.endswith(forbidden), f'compiled/cache artifact included: {name}'
    assert '__pycache__' not in Path(name).parts, f'cache directory included: {name}'
assert not any(Path(name).name=='aeneas-r363-instantiated-pattern-candidate' for name in files)
rows=[]
for line in (ROOT/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert name in files, f'checksum names missing file: {name}'
    assert sha(files[name])==digest, f'checksum mismatch: {name}'
    rows.append(name)
assert set(rows)==set(files), 'checksum index does not cover the exact package file set'
manifest=json.loads((ROOT/'inventory.json').read_text())
items={row['package_path']:row for row in manifest['items']}
assert set(items)==set(files)-{'inventory.json'}, 'inventory does not cover package artifacts (excluding itself)'
for name,row in items.items():
    assert sha(files[name])==row['sha256'], f'inventory hash mismatch: {name}'
    assert files[name].stat().st_size==row['size_bytes'], f'inventory size mismatch: {name}'
# Cross-check key saved outcomes without making semantic conclusions.
build=json.loads((ROOT/'r363/build-outcome.json').read_text())
assert build['build_status']==0 and build['binary_sha256']=='3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
translation=json.loads((ROOT/'r364-translation/result.json').read_text())
assert translation['exit_status']==0 and translation['Lean_compiled'] is False
assert translation['binary_sha256']==build['binary_sha256']
census=json.loads((ROOT/'r364-generated-source-census/census.json').read_text())
assert census['llbc']['sha256']==translation['source_sha256'] and census['llbc']['has_errors'] is False
print(json.dumps({'status':'PASS','verified_package_files':len(files),'checksum_entries':len(rows),'compiled_or_cache_artifacts':0,'build_status':build['build_status'],'translation_status':translation['exit_status'],'Lean_compiled':False},indent=2))
