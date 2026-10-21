#!/usr/bin/env python3
import hashlib,json,pathlib,sys
r=pathlib.Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text());errs=[]
for f in m.get("files",[]):
 p=r/f["path"]
 if not p.is_file(): errs.append("missing "+f["path"]);continue
 b=p.read_bytes()
 if hashlib.sha256(b).hexdigest()!=f["sha256"] or len(b)!=f["size_bytes"]:errs.append("file pin mismatch "+f["path"])
for x in m.get("modules",[]):
 p=r/x["source"];q=r/x["receipt"]
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=x["source_sha256"]:errs.append("source mismatch "+x["module"]);continue
 if not q.is_file():errs.append("missing receipt "+x["module"]);continue
 z=json.loads(q.read_text())
 if z.get("exit_status")!=0:errs.append("non-green receipt "+x["module"])
 if z.get("source_sha256") and z["source_sha256"]!=x["source_sha256"]:errs.append("receipt source mismatch "+x["module"])
 if z.get("object_sha256") and z["object_sha256"]!=x["object_sha256"]:errs.append("receipt object mismatch "+x["module"])
 if not x.get("object_sha256"):errs.append("missing object pin "+x["module"])
if errs:print("FAIL\n"+"\n".join(errs));sys.exit(1)
print("PASS",len(m.get("files",[])),"files",len(m.get("modules",[])),"owners")
