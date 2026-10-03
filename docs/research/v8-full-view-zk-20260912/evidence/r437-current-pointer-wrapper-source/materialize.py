#!/usr/bin/env python3
"""Verify package hashes and materialize its losslessly compressed LLBC."""
import argparse,gzip,hashlib,json,pathlib,shutil
ROOT=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('destination',type=pathlib.Path);args=ap.parse_args()
assert not args.destination.exists(),'destination must be fresh'
sha=lambda b:hashlib.sha256(b).hexdigest()
physical=json.loads((ROOT/'SHA256SUMS.json').read_text())
for rel,digest in physical.items():assert sha((ROOT/rel).read_bytes())==digest,rel
manifest=json.loads((ROOT/'compression-manifest.json').read_text());stored={x['stored_path']:x for x in manifest['artifacts']}
args.destination.mkdir(parents=True)
for p in ROOT.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(ROOT).as_posix();e=stored.get(rel)
 if e:
  raw=gzip.decompress(p.read_bytes());assert sha(raw)==e['sha256_uncompressed'] and len(raw)==e['uncompressed_bytes']
  q=args.destination/e['original_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 else:
  q=args.destination/p.relative_to(ROOT);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
print('Verified and materialized:',args.destination)
