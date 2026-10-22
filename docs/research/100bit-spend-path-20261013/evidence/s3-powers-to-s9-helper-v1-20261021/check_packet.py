#!/usr/bin/env python3
import hashlib,json,pathlib,sys
root=pathlib.Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for rel,meta in m["files"].items():
 p=root/rel; assert p.is_file(), rel
 b=p.read_bytes(); assert len(b)==meta["bytes"], rel
 assert hashlib.sha256(b).hexdigest()==meta["sha256"], rel
for name,meta in m["direct_import_source_map"].items():
 for key,pathkey in (("source_sha256","source"),("producer_receipt_sha256","producer_receipt")):
  p=root/meta[pathkey]; assert p.is_file(), (name,pathkey)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==meta[key], (name,key)
mod=m["modules"][0]; assert hashlib.sha256((root/mod["source"]).read_bytes()).hexdigest()==mod["source_sha256"]
assert hashlib.sha256((root/mod["producer_receipt"]).read_bytes()).hexdigest()==hashlib.sha256((root/"attempt/receipt.json").read_bytes()).hexdigest()
print("source-only packet hashes PASS")
