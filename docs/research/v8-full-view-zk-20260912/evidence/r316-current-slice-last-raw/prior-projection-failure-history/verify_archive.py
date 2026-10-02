#!/usr/bin/env python3
"""Verify saved R298/R300 copies and archive checksums; no builds or translations."""
import hashlib,json
from pathlib import Path
A=Path(__file__).resolve().parent; ROOT=A.parents[1]; SRC=ROOT/'.r21-scratch'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for n in ['r298-slice-last-inventory','r300-slice-last-translation']:
 s=SRC/n; d=A/'artifacts'/n
 sf={p.relative_to(s).as_posix() for p in s.rglob('*') if p.is_file()}
 df={p.relative_to(d).as_posix() for p in d.rglob('*') if p.is_file()}
 assert sf==df,(n,sf-df,df-sf)
 for rel in sf: assert sha(s/rel)==sha(d/rel),(n,rel)
 checks.append({'directory':n,'files':len(sf),'byte_identical':True})
correction=SRC/'r300-slice-last-translation/revision-correction.json'; archived=A/'artifacts/r300-slice-last-translation/revision-correction.json'
assert sha(correction)==sha(archived)
manifest=json.loads((A/'manifest.json').read_text())
assert manifest['current_actual_repository_revision']=='04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43'
entries=[]
for line in (A/'SHA256SUMS').read_text().splitlines():
 want,rel=line.split('  ',1); p=A/rel; entries.append((rel,p.is_file() and sha(p)==want))
assert entries and all(ok for _,ok in entries)
report={'all_passed':True,'source_directory_checks':checks,'R300_revision_correction_receipt_byte_identical':True,'archive_checksum_entries_checked':len(entries),'archive_checksum_mismatches':[]}
(A/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
