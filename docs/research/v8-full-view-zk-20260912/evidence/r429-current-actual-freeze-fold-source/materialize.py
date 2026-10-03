#!/usr/bin/env python3
"""Verify and materialize exact saved evidence in a fresh directory; no jobs run."""
import argparse,gzip,hashlib,json,pathlib,shutil
ROOT=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('destination',type=pathlib.Path);args=ap.parse_args()
assert not args.destination.exists(),'destination must be fresh'
def sha(b):return hashlib.sha256(b).hexdigest()
def relative(s):
 p=pathlib.PurePosixPath(s);assert not p.is_absolute() and '..' not in p.parts;return p
index=json.loads((ROOT/'SHA256SUMS.json').read_text())
for p,h in index.items():assert sha((ROOT/relative(p)).read_bytes())==h,p
manifest=json.loads((ROOT/'compression-manifest.json').read_text());storage={e['stored_path']:e for e in manifest['artifacts']}
args.destination.mkdir(parents=True)
for p in ROOT.rglob('*'):
 if not p.is_file():continue
 rel=str(p.relative_to(ROOT));entry=storage.get(rel)
 if entry:
  raw=gzip.decompress(p.read_bytes());assert sha(raw)==entry['sha256_uncompressed'];assert len(raw)==entry['uncompressed_bytes'];target=args.destination/relative(entry['original_path']);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
 else:
  target=args.destination/p.relative_to(ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
print('Verified physical index and all compressed raw hashes; materialized',args.destination)
