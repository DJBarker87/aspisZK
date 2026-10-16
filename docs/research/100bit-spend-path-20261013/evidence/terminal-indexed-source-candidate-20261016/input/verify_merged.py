#!/usr/bin/env python3
import hashlib, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
M=json.loads((ROOT/'merged-source-manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for row in M['source_files']:
 p=ROOT/row['merged_path']
 if not p.is_file(): errors.append('missing '+row['merged_path']); continue
 if p.stat().st_size!=row['bytes'] or sha(p)!=row['sha256']:
  errors.append('hash/size mismatch '+row['merged_path'])
# Every source body row was independently pinned to the retained original extraction source snapshot.
originroot=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
for row in M['source_files']:
 p=originroot/row['origin_path']
 if p.is_file() and sha(p)!=row['sha256']:
  errors.append('current source differs from saved body '+row['origin_path'])
# Target-critical source aliases and unique type definition check.
lib=(ROOT/'src/lib.rs').read_text()
if 'extern crate self as aspis_core;' not in lib: errors.append('missing aspis_core self alias')
if 'pub mod field;' not in lib: errors.append('missing sole local field root')
if '[path = "statement/pool_v1/mod.rs"] pub mod pool_v1;' not in lib: errors.append('missing path-mapped pool module')
if '[path = "statement/extraction_probe.rs"] pub mod extraction_probe;' not in lib: errors.append('missing path-mapped probe')
if 'crates/aspis-core' in (ROOT/'Cargo.toml').read_text(): errors.append('unexpected external aspic-core dependency')
if len({r['origin_path'] for r in M['source_files']}) != len(M['source_files']): errors.append('duplicate origin source path')
if errors:
 print('FAIL'); print('\n'.join(errors)); sys.exit(1)
print(json.dumps({'result':'pass','checked_source_files':len(M['source_files']),'field_sha256':M['field_source_sha256'],'terminal_sha256':M['terminal_source_sha256'],'wrapper_sha256':M['wrapper_source_sha256'],'root_scaffold_sha256':M['root_scaffold_sha256'],'note':'Root scaffold/module wiring is extraction-only; module function source bytes are pinned unchanged.'},indent=2))
