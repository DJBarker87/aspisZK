#!/usr/bin/env python3
import hashlib,json,pathlib,sys
p=pathlib.Path(__file__).resolve().parent;m=json.loads((p/"manifest.json").read_text())
for x in m["modules"]:
 s=p/x["source"]
 assert hashlib.sha256(s.read_bytes()).hexdigest()==x["source_sha256"]
 r=json.loads((p/x["receipt"]).read_text())
 assert r["exit_status"]==0 and r["object_sha256"]==x["object_sha256"]
 assert r["source_sha256"]==x["source_sha256"]
for rel in ("manifest.json","README.md","check_packet.py",*[x["source"] for x in m["modules"]],*[x["receipt"] for x in m["modules"]],*[x["preflight"] for x in m["modules"]],*[x["time_log"] for x in m["modules"]],*["receipts/"+m["modules"][0]["name"]+".lean.log"]):
 assert (p/rel).is_file(),rel
print("packet metadata and source checks pass")
