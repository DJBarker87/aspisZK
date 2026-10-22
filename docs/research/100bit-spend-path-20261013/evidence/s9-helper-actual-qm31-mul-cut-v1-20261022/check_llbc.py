from pathlib import Path
import json
W=Path(__file__).resolve().parent
d=json.loads((W/"runs-charon/helper-projection.llbc").read_text())
assert not d.get("has_errors")
t=d["translated"]
required={
 "QM31.mul":("pub fn mul(self, rhs: QM31) -> QM31",935),
 "CM31.mul":("pub fn mul(self, rhs: CM31) -> CM31",306),
 "CM31.add":("pub fn add(self, rhs: CM31) -> CM31",281),
 "CM31.sub":("pub fn sub(self, rhs: CM31) -> CM31",289),
 "M31.add":("pub fn add(self, rhs: M31) -> M31",62),
 "M31.sub":("pub fn sub(self, rhs: M31) -> M31",94),
 "M31.mul":("pub fn mul(self, rhs: M31) -> M31",133),
 "M31.reduce_u64":("fn reduce_u64(x: u64) -> u32",31),
 "mul_by_r":("fn mul_by_r(x: CM31) -> CM31",860),
}
found={}
for f in t["fun_decls"]:
 m=f.get("item_meta") or {}; text=m.get("source_text") or ""; span=m.get("span",{}).get("data",{}); beg=(span.get("beg") or {}).get("line")
 for name,(needle,line) in required.items():
  if needle in text and beg==line: found[name]=m.get("opacity")
assert set(found)==set(required),(found,required)
assert all(v=="Transparent" for v in found.values()),found
assert t["fun_decls"] and t["type_decls"],"empty LLBC body/type set"
print(json.dumps({"required_actual_arithmetic":found,"function_count":len(t["fun_decls"]),"type_count":len(t["type_decls"])}))
