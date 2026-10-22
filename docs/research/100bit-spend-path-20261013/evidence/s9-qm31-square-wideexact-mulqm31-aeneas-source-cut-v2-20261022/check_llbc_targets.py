from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
ll=R/"runs-charon/helper-projection.llbc"
d=json.loads(ll.read_text()); assert not d.get("has_errors",True)
t=d["translated"]
files={i:f.get("name",{}).get("Local","") for i,f in enumerate(t["files"])}
ident=json.loads((R/"source-identities.json").read_text())
selected=ident["selected_transparent_targets"]
found={}
for f in t["fun_decls"]:
 m=f["item_meta"]; span=m["span"]["data"]; fid=span["file_id"]; src=m.get("source_text") or ""
 for label,pin in selected.items():
  if pin["method_text"] in src:
   assert m["opacity"]=="Transparent",(label,m["opacity"])
   assert isinstance(f["body"],dict) and "Structured" in f["body"],(label,f.get("body"))
   found[label]={"def_id":f["def_id"],"file":files[fid],"source_line":span["beg"]["line"],"opacity":m["opacity"],"method_body_sha256":pin["method_body_sha256"],"source_text_sha256":hashlib.sha256(src.encode()).hexdigest()}
assert set(found)==set(selected),(set(found),set(selected))
field_ids={i for i,n in files.items() if n.endswith("field.rs") or n.endswith("wide_exact.rs")}
field_funs=[]
for f in t["fun_decls"]:
 m=f["item_meta"]; fid=m["span"]["data"]["file_id"]
 if fid in field_ids:
  assert m["opacity"]=="Transparent",(f["def_id"],files[fid],m["opacity"],m["span"]["data"]["beg"]["line"])
  field_funs.append({"def_id":f["def_id"],"file":files[fid],"line":m["span"]["data"]["beg"]["line"],"opacity":m["opacity"]})
assert field_funs, "no source field declarations found"
out={"schema":"s9-focused-transparent-field-cut-inventory-v1","llbc_sha256":hashlib.sha256(ll.read_bytes()).hexdigest(),"llbc_bytes":ll.stat().st_size,"has_errors":d.get("has_errors"),"fun_count":len(t["fun_decls"]),"type_count":len(t["type_decls"]),"selected_transparent_targets":found,"all_source_field_functions_transparent":True,"source_field_function_count":len(field_funs),"source_field_functions":field_funs}
(R/"runs-charon/declaration-inventory.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
