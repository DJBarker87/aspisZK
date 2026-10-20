#!/usr/bin/env python3
import hashlib,json,pathlib
p=pathlib.Path(__file__).resolve().parent;m=json.loads((p/"manifest.json").read_text())
for x in m["modules"]:
 s=p/x["source"]; assert hashlib.sha256(s.read_bytes()).hexdigest()==x["source_sha256"]
 r=json.loads((p/x["receipt"]).read_text()); assert r["exit_status"]==0 and r["source_sha256"]==x["source_sha256"] and r["object_sha256"]==x["object_sha256"]
for x in m["files"]: assert hashlib.sha256((p/x["path"]).read_bytes()).hexdigest()==x["sha256"]
print("packet metadata/source/checksums pass")
