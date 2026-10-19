#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parent
KIT=ROOT/'input'
WT=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((KIT/'source-pins.json').read_text())
missing=[]; mismatches=[]
for row in m['transitive_source_pins']:
    orig=WT/row['origin_path']; copy=KIT/row['copy_path']
    if not orig.is_file() or not copy.is_file(): missing.append(row['origin_path']); continue
    if sha(orig)!=row['sha256']: mismatches.append('origin pin drift '+row['origin_path'])
    if sha(copy)!=row['copy_sha256']: mismatches.append('copy pin drift '+row['copy_path'])
    if row.get('exact') is True and sha(orig)!=sha(copy): mismatches.append('copy differs '+row['origin_path'])
lib=next(r for r in m['transitive_source_pins'] if r['origin_path']=='crates/aspis-statement/src/lib.rs')
backup=KIT/lib['original_backup_path']; scaffold=KIT/lib['copy_path']
if sha(backup)!=lib['original_backup_sha256'] or backup.read_bytes()!=(WT/lib['origin_path']).read_bytes(): mismatches.append('original lib backup mismatch')
expected=backup.read_bytes()+b'\n#[cfg(feature = "r0")]\npub mod extraction_probe;\n'
if scaffold.read_bytes()!=expected: mismatches.append('statement lib scaffold differs beyond module append')
if sha(KIT/'crates/aspis-statement/src/extraction_probe.rs')!=m['wrapper']['sha256']: mismatches.append('wrapper pin mismatch')
if sha(WT/'Cargo.lock')!=m['lock']['origin_sha256'] or sha(KIT/'Cargo.lock')!=m['lock']['sha256']: mismatches.append('lock pin mismatch')
if missing or mismatches:
    print(json.dumps({'missing':missing,'mismatches':mismatches},indent=2)); sys.exit(1)
print(json.dumps({'status':'PASS_SOURCE_ONLY_PREFLIGHT','source_files_checked':len(m['transitive_source_pins']),'wrapper_sha256':m['wrapper']['sha256'],'source_revision_recorded':m['source_revision'],'build_or_extraction_run':False},indent=2))
