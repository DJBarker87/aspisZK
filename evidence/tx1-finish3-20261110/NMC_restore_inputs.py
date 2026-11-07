"""Validate compacted historical inputs; optionally restore their exact bytes."""
from pathlib import Path
import hashlib,json,lzma,sys
E=Path(__file__).resolve().parent
assert sys.argv[1:]in [[],['--materialize']]
manifest=json.loads((E/'NMC_INPUT_REFERENCES.json').read_text())
for row in manifest['references']:
 target=E/row['retained'];dest=E/row['path']
 assert target.resolve().is_relative_to(E)and dest.resolve().is_relative_to(E)
 blob=target.read_bytes()
 if row['encoding']=='xz':blob=lzma.decompress(blob)
 else:assert row['encoding']=='identity'
 assert hashlib.sha256(blob).hexdigest()==row['sha256']and len(blob)==row['bytes']
 if dest.exists():assert dest.read_bytes()==blob
 elif sys.argv[1:]:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
print(json.dumps(dict(status='PASS_EXACT_REFERENCED_INPUTS',references=len(manifest['references']),materialized=bool(sys.argv[1:]),proofs_launched=0)))
