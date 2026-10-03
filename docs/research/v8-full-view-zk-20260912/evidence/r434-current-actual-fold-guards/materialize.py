#!/usr/bin/env python3
"""Verify physical package hashes and materialize compressed raw artifacts."""
import argparse,gzip,hashlib,json,pathlib,shutil
ROOT=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('destination',type=pathlib.Path);args=ap.parse_args()
assert not args.destination.exists(),'destination must be fresh'
def sha(b):return hashlib.sha256(b).hexdigest()
def rel(s):
 p=pathlib.PurePosixPath(s);assert not p.is_absolute() and '..' not in p.parts;return p
physical=json.loads((ROOT/'SHA256SUMS.json').read_text())
for p,h in physical.items():assert sha((ROOT/rel(p)).read_bytes())==h,p
manifest=json.loads((ROOT/'compression-manifest.json').read_text());stored={a['stored_path']:a for a in manifest['artifacts']}
args.destination.mkdir(parents=True)
for p in ROOT.rglob('*'):
 if not p.is_file():continue
 name=str(p.relative_to(ROOT));e=stored.get(name)
 if e:
  raw=gzip.decompress(p.read_bytes());assert sha(raw)==e['sha256_uncompressed'] and len(raw)==e['uncompressed_bytes'];q=args.destination/rel(e['original_path']);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 else:
  q=args.destination/p.relative_to(ROOT);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
print('Verified physical hashes and materialized exact compressed evidence:',args.destination)
