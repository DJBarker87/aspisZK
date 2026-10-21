from pathlib import Path
import hashlib,json
root=Path(__file__).parent
m=json.loads((root/"manifest.json").read_text())
for rel,key in [(m["source_path"],"source_sha256"),("receipt/command.json",None),("receipt/receipt.json",None),("receipt/time.log",None),("receipt/lean.log",None)]:
 p=root/rel; assert p.is_file(),rel
 if key: assert hashlib.sha256(p.read_bytes()).hexdigest()==m[key],rel
assert m["exit_status"]==0 and m["swap_bytes"]==0
assert hashlib.sha256((root/"receipt/LEAN_PATH.txt").read_bytes()).hexdigest()==m["lean_path_sha256"]
assert (root/"receipt/LEAN_PATH.txt").read_text()==json.loads((root/"receipt/command.json").read_text())["lean_path"]
obj=Path(m["object_path"]); assert obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest()==m["object_sha256"]
assert m["axioms"]==["propext","Classical.choice","Quot.sound"]
for mod,row in m["direct_import_source_map"].items():
 sp=Path(row["source_path"]); op=Path(row["selected_object_path"])
 if not sp.is_absolute(): sp=root.parent.parent/sp
 sp=sp.resolve()
 assert sp.is_file(),(mod,sp)
 assert hashlib.sha256(sp.read_bytes()).hexdigest()==row["source_sha256"],(mod,"source")
 assert op.is_file(),(mod,op)
 assert hashlib.sha256(op.read_bytes()).hexdigest()==row["object_sha256"],(mod,"object")
print("packet source/receipt/direct-owner hashes PASS")
